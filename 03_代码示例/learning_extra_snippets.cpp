#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

std::vector<int> buildLps(const std::string& pattern) {
    std::vector<int> lps(pattern.size(), 0);
    for (int i = 1, len = 0; i < static_cast<int>(pattern.size());) {
        if (pattern[i] == pattern[len]) {
            lps[i++] = ++len;
        } else if (len > 0) {
            len = lps[len - 1];
        } else {
            lps[i++] = 0;
        }
    }
    return lps;
}

int kmpSearch(const std::string& text, const std::string& pattern) {
    if (pattern.empty()) return 0;
    auto lps = buildLps(pattern);
    for (int i = 0, j = 0; i < static_cast<int>(text.size());) {
        if (text[i] == pattern[j]) {
            ++i;
            ++j;
            if (j == static_cast<int>(pattern.size())) return i - j;
        } else if (j > 0) {
            j = lps[j - 1];
        } else {
            ++i;
        }
    }
    return -1;
}

class DSU {
public:
    explicit DSU(int n) : parent_(n), rank_(n, 0) {
        std::iota(parent_.begin(), parent_.end(), 0);
    }

    int find(int x) {
        if (parent_[x] != x) parent_[x] = find(parent_[x]);
        return parent_[x];
    }

    bool unite(int a, int b) {
        int ra = find(a);
        int rb = find(b);
        if (ra == rb) return false;
        if (rank_[ra] < rank_[rb]) std::swap(ra, rb);
        parent_[rb] = ra;
        if (rank_[ra] == rank_[rb]) ++rank_[ra];
        return true;
    }

private:
    std::vector<int> parent_;
    std::vector<int> rank_;
};

class Trie {
public:
    void insert(const std::string& word) {
        Node* cur = &root_;
        for (char c : word) {
            auto& next = cur->child[c];
            if (!next) next = std::make_unique<Node>();
            cur = next.get();
        }
        cur->end = true;
    }

    bool search(const std::string& word) const {
        const Node* node = findNode(word);
        return node && node->end;
    }

    bool startsWith(const std::string& prefix) const {
        return findNode(prefix) != nullptr;
    }

private:
    struct Node {
        bool end = false;
        std::unordered_map<char, std::unique_ptr<Node>> child;
    };

    const Node* findNode(const std::string& s) const {
        const Node* cur = &root_;
        for (char c : s) {
            auto it = cur->child.find(c);
            if (it == cur->child.end()) return nullptr;
            cur = it->second.get();
        }
        return cur;
    }

    Node root_;
};

class FrameDecoder {
public:
    void append(const char* data, size_t n) {
        buffer_.append(data, n);
    }

    std::vector<std::string> decode() {
        std::vector<std::string> frames;
        while (true) {
            if (buffer_.size() < 4) break;
            uint32_t len = readUint32BE(buffer_.data());
            if (len > max_frame_) throw std::runtime_error("frame too large");
            if (buffer_.size() < 4 + len) break;
            frames.push_back(buffer_.substr(4, len));
            buffer_.erase(0, 4 + len);
        }
        return frames;
    }

private:
    static uint32_t readUint32BE(const char* p) {
        return (static_cast<uint32_t>(static_cast<unsigned char>(p[0])) << 24) |
               (static_cast<uint32_t>(static_cast<unsigned char>(p[1])) << 16) |
               (static_cast<uint32_t>(static_cast<unsigned char>(p[2])) << 8) |
               static_cast<uint32_t>(static_cast<unsigned char>(p[3]));
    }

    std::string buffer_;
    const uint32_t max_frame_ = 16 * 1024 * 1024;
};

struct Timer {
    int id;
    int64_t expire_ms;
    std::function<void()> callback;
    bool cancelled = false;
};

struct TimerCompare {
    bool operator()(const std::shared_ptr<Timer>& a,
                    const std::shared_ptr<Timer>& b) const {
        return a->expire_ms > b->expire_ms;
    }
};

class TimerHeap {
public:
    int add(int64_t expire_ms, std::function<void()> callback) {
        auto timer = std::make_shared<Timer>();
        timer->id = ++next_id_;
        timer->expire_ms = expire_ms;
        timer->callback = std::move(callback);
        timers_[timer->id] = timer;
        heap_.push(timer);
        return timer->id;
    }

    void cancel(int id) {
        auto it = timers_.find(id);
        if (it == timers_.end()) return;
        it->second->cancelled = true;
        timers_.erase(it);
    }

    void runExpired(int64_t now_ms) {
        while (!heap_.empty()) {
            auto timer = heap_.top();
            if (timer->cancelled) {
                heap_.pop();
                continue;
            }
            if (timer->expire_ms > now_ms) break;
            heap_.pop();
            timers_.erase(timer->id);
            timer->callback();
        }
    }

private:
    int next_id_ = 0;
    std::priority_queue<
        std::shared_ptr<Timer>,
        std::vector<std::shared_ptr<Timer>>,
        TimerCompare> heap_;
    std::unordered_map<int, std::shared_ptr<Timer>> timers_;
};

class FixedBlockPool {
public:
    explicit FixedBlockPool(size_t block_size)
        : block_size_(std::max(block_size, sizeof(Node))) {}

    FixedBlockPool(const FixedBlockPool&) = delete;
    FixedBlockPool& operator=(const FixedBlockPool&) = delete;

    ~FixedBlockPool() {
        for (void* chunk : chunks_) {
            ::operator delete(chunk);
        }
    }

    void* allocate() {
        if (!free_) refill();
        Node* node = free_;
        free_ = free_->next;
        return node;
    }

    void deallocate(void* p) {
        if (!p) return;
        auto* node = static_cast<Node*>(p);
        node->next = free_;
        free_ = node;
    }

private:
    struct Node {
        Node* next;
    };

    void refill() {
        constexpr size_t kBatch = 64;
        char* chunk = static_cast<char*>(::operator new(block_size_ * kBatch));
        chunks_.push_back(chunk);
        for (size_t i = 0; i < kBatch; ++i) {
            deallocate(chunk + i * block_size_);
        }
    }

    size_t block_size_;
    Node* free_ = nullptr;
    std::vector<void*> chunks_;
};

template <class T>
class ObjectPool {
public:
    using Ptr = std::unique_ptr<T, std::function<void(T*)>>;

    template <class... Args>
    Ptr acquire(Args&&... args) {
        T* obj = nullptr;
        if (!free_.empty()) {
            obj = free_.back();
            free_.pop_back();
            *obj = T(std::forward<Args>(args)...);
        } else {
            storage_.push_back(std::make_unique<T>(std::forward<Args>(args)...));
            obj = storage_.back().get();
        }
        return Ptr(obj, [this](T* p) { release(p); });
    }

private:
    void release(T* p) {
        free_.push_back(p);
    }

    std::vector<std::unique_ptr<T>> storage_;
    std::vector<T*> free_;
};

std::vector<int> topoSort(int n, const std::vector<std::pair<int, int>>& edges) {
    std::vector<std::vector<int>> graph(n);
    std::vector<int> indegree(n, 0);
    for (auto [u, v] : edges) {
        graph[u].push_back(v);
        ++indegree[v];
    }

    std::queue<int> q;
    for (int i = 0; i < n; ++i) {
        if (indegree[i] == 0) q.push(i);
    }

    std::vector<int> order;
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        order.push_back(u);
        for (int v : graph[u]) {
            if (--indegree[v] == 0) q.push(v);
        }
    }
    if (static_cast<int>(order.size()) != n) return {};
    return order;
}

int lowerBound(const std::vector<int>& nums, int target) {
    int l = 0;
    int r = static_cast<int>(nums.size());
    while (l < r) {
        int mid = l + (r - l) / 2;
        if (nums[mid] >= target) r = mid;
        else l = mid + 1;
    }
    return l;
}

int lengthOfLIS(const std::vector<int>& nums) {
    std::vector<int> tails;
    for (int x : nums) {
        auto it = std::lower_bound(tails.begin(), tails.end(), x);
        if (it == tails.end()) tails.push_back(x);
        else *it = x;
    }
    return static_cast<int>(tails.size());
}

#ifdef LEARNING_EXTRA_SNIPPETS_DEMO
#include <iostream>

int main() {
    std::cout << kmpSearch("hello interview", "inter") << "\n";
    DSU dsu(3);
    dsu.unite(0, 1);
    std::cout << (dsu.find(0) == dsu.find(1)) << "\n";
    return 0;
}
#endif
