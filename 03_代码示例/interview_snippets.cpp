#include <algorithm>
#include <condition_variable>
#include <functional>
#include <future>
#include <iostream>
#include <iterator>
#include <list>
#include <limits>
#include <memory>
#include <mutex>
#include <optional>
#include <queue>
#include <stdexcept>
#include <string>
#include <thread>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

struct ListNode {
    int val;
    ListNode* next;
    explicit ListNode(int x) : val(x), next(nullptr) {}
};

ListNode* reverseList(ListNode* head) {
    ListNode* prev = nullptr;
    while (head) {
        ListNode* next = head->next;
        head->next = prev;
        prev = head;
        head = next;
    }
    return prev;
}

ListNode* detectCycle(ListNode* head) {
    ListNode* slow = head;
    ListNode* fast = head;
    while (fast && fast->next) {
        slow = slow->next;
        fast = fast->next->next;
        if (slow == fast) {
            ListNode* p = head;
            while (p != slow) {
                p = p->next;
                slow = slow->next;
            }
            return p;
        }
    }
    return nullptr;
}

ListNode* mergeTwoLists(ListNode* a, ListNode* b) {
    ListNode dummy(0);
    ListNode* tail = &dummy;
    while (a && b) {
        if (a->val <= b->val) {
            tail->next = a;
            a = a->next;
        } else {
            tail->next = b;
            b = b->next;
        }
        tail = tail->next;
    }
    tail->next = a ? a : b;
    return dummy.next;
}

ListNode* removeNthFromEnd(ListNode* head, int n) {
    ListNode dummy(0);
    dummy.next = head;
    ListNode* fast = &dummy;
    ListNode* slow = &dummy;
    for (int i = 0; i < n && fast; ++i) fast = fast->next;
    if (!fast) return head;
    while (fast->next) {
        fast = fast->next;
        slow = slow->next;
    }
    ListNode* victim = slow->next;
    slow->next = victim ? victim->next : nullptr;
    return dummy.next;
}

int binarySearchLowerBound(const std::vector<int>& nums, int target) {
    int l = 0;
    int r = static_cast<int>(nums.size());
    while (l < r) {
        int mid = l + (r - l) / 2;
        if (nums[mid] >= target) r = mid;
        else l = mid + 1;
    }
    return l;
}

int lengthOfLongestSubstring(const std::string& s) {
    std::vector<int> last(256, -1);
    int left = 0;
    int ans = 0;
    for (int right = 0; right < static_cast<int>(s.size()); ++right) {
        unsigned char ch = static_cast<unsigned char>(s[right]);
        if (last[ch] >= left) left = last[ch] + 1;
        last[ch] = right;
        ans = std::max(ans, right - left + 1);
    }
    return ans;
}

std::vector<std::vector<int>> threeSum(std::vector<int> nums) {
    std::sort(nums.begin(), nums.end());
    std::vector<std::vector<int>> ans;
    const int n = static_cast<int>(nums.size());
    for (int i = 0; i < n; ++i) {
        if (i > 0 && nums[i] == nums[i - 1]) continue;
        int l = i + 1;
        int r = n - 1;
        while (l < r) {
            long long sum = static_cast<long long>(nums[i]) + nums[l] + nums[r];
            if (sum == 0) {
                ans.push_back({nums[i], nums[l], nums[r]});
                while (l < r && nums[l] == nums[l + 1]) ++l;
                while (l < r && nums[r] == nums[r - 1]) --r;
                ++l;
                --r;
            } else if (sum < 0) {
                ++l;
            } else {
                --r;
            }
        }
    }
    return ans;
}

int findKthLargest(std::vector<int> nums, int k) {
    if (k <= 0 || k > static_cast<int>(nums.size())) {
        throw std::invalid_argument("invalid k");
    }
    auto target = nums.end() - k;
    std::nth_element(nums.begin(), target, nums.end());
    return *target;
}

void quickSort(std::vector<int>& a, int l, int r) {
    if (l >= r) return;
    int i = l;
    int j = r;
    int pivot = a[l + (r - l) / 2];
    while (i <= j) {
        while (a[i] < pivot) ++i;
        while (a[j] > pivot) --j;
        if (i <= j) std::swap(a[i++], a[j--]);
    }
    if (l < j) quickSort(a, l, j);
    if (i < r) quickSort(a, i, r);
}

std::vector<int> mergeSort(std::vector<int> a) {
    if (a.size() <= 1) return a;
    int mid = static_cast<int>(a.size() / 2);
    std::vector<int> left(a.begin(), a.begin() + mid);
    std::vector<int> right(a.begin() + mid, a.end());
    left = mergeSort(std::move(left));
    right = mergeSort(std::move(right));
    std::vector<int> ans;
    ans.reserve(a.size());
    std::merge(left.begin(), left.end(), right.begin(), right.end(), std::back_inserter(ans));
    return ans;
}

class LRUCache {
public:
    explicit LRUCache(size_t capacity) : capacity_(capacity) {}

    std::optional<int> get(int key) {
        auto it = map_.find(key);
        if (it == map_.end()) return std::nullopt;
        items_.splice(items_.begin(), items_, it->second);
        return it->second->second;
    }

    void put(int key, int value) {
        if (capacity_ == 0) return;
        auto it = map_.find(key);
        if (it != map_.end()) {
            it->second->second = value;
            items_.splice(items_.begin(), items_, it->second);
            return;
        }
        if (items_.size() == capacity_) {
            auto [old_key, old_value] = items_.back();
            (void)old_value;
            map_.erase(old_key);
            items_.pop_back();
        }
        items_.emplace_front(key, value);
        map_[key] = items_.begin();
    }

private:
    size_t capacity_;
    std::list<std::pair<int, int>> items_;
    std::unordered_map<int, std::list<std::pair<int, int>>::iterator> map_;
};

template <class T>
class BlockingQueue {
public:
    explicit BlockingQueue(size_t capacity) : capacity_(capacity) {}

    bool push(T value) {
        std::unique_lock<std::mutex> lk(mu_);
        not_full_.wait(lk, [&] { return closed_ || queue_.size() < capacity_; });
        if (closed_) return false;
        queue_.push(std::move(value));
        not_empty_.notify_one();
        return true;
    }

    bool pop(T& out) {
        std::unique_lock<std::mutex> lk(mu_);
        not_empty_.wait(lk, [&] { return closed_ || !queue_.empty(); });
        if (queue_.empty()) return false;
        out = std::move(queue_.front());
        queue_.pop();
        not_full_.notify_one();
        return true;
    }

    void close() {
        {
            std::lock_guard<std::mutex> lk(mu_);
            closed_ = true;
        }
        not_empty_.notify_all();
        not_full_.notify_all();
    }

private:
    size_t capacity_;
    bool closed_ = false;
    std::queue<T> queue_;
    std::mutex mu_;
    std::condition_variable not_empty_;
    std::condition_variable not_full_;
};

class ThreadPool {
public:
    explicit ThreadPool(size_t n) {
        if (n == 0) throw std::invalid_argument("thread count must be positive");
        for (size_t i = 0; i < n; ++i) {
            workers_.emplace_back([this] { workerLoop(); });
        }
    }

    ThreadPool(const ThreadPool&) = delete;
    ThreadPool& operator=(const ThreadPool&) = delete;

    ~ThreadPool() {
        {
            std::lock_guard<std::mutex> lk(mu_);
            stopped_ = true;
        }
        cv_.notify_all();
        for (auto& worker : workers_) {
            if (worker.joinable()) worker.join();
        }
    }

    template <class F, class... Args>
    auto submit(F&& f, Args&&... args)
        -> std::future<std::invoke_result_t<F, Args...>> {
        using Ret = std::invoke_result_t<F, Args...>;
        auto task = std::make_shared<std::packaged_task<Ret()>>(
            std::bind(std::forward<F>(f), std::forward<Args>(args)...));
        std::future<Ret> fut = task->get_future();
        {
            std::lock_guard<std::mutex> lk(mu_);
            if (stopped_) throw std::runtime_error("submit on stopped ThreadPool");
            tasks_.emplace([task] { (*task)(); });
        }
        cv_.notify_one();
        return fut;
    }

private:
    void workerLoop() {
        while (true) {
            std::function<void()> task;
            {
                std::unique_lock<std::mutex> lk(mu_);
                cv_.wait(lk, [&] { return stopped_ || !tasks_.empty(); });
                if (stopped_ && tasks_.empty()) return;
                task = std::move(tasks_.front());
                tasks_.pop();
            }
            try {
                task();
            } catch (...) {
                // packaged_task 会把异常传给 future；这里兜底防止普通任务杀死 worker。
            }
        }
    }

    bool stopped_ = false;
    std::mutex mu_;
    std::condition_variable cv_;
    std::queue<std::function<void()>> tasks_;
    std::vector<std::thread> workers_;
};

class Singleton {
public:
    static Singleton& instance() {
        static Singleton obj;
        return obj;
    }
    Singleton(const Singleton&) = delete;
    Singleton& operator=(const Singleton&) = delete;

private:
    Singleton() = default;
};

struct TreeNode {
    int val;
    TreeNode* left;
    TreeNode* right;
    explicit TreeNode(int x) : val(x), left(nullptr), right(nullptr) {}
};

std::vector<std::vector<int>> levelOrder(TreeNode* root) {
    std::vector<std::vector<int>> ans;
    if (!root) return ans;
    std::queue<TreeNode*> q;
    q.push(root);
    while (!q.empty()) {
        int size = static_cast<int>(q.size());
        std::vector<int> level;
        level.reserve(size);
        for (int i = 0; i < size; ++i) {
            TreeNode* node = q.front();
            q.pop();
            level.push_back(node->val);
            if (node->left) q.push(node->left);
            if (node->right) q.push(node->right);
        }
        ans.push_back(std::move(level));
    }
    return ans;
}

int maxDepth(TreeNode* root) {
    if (!root) return 0;
    return 1 + std::max(maxDepth(root->left), maxDepth(root->right));
}

TreeNode* lowestCommonAncestor(TreeNode* root, TreeNode* p, TreeNode* q) {
    if (!root || root == p || root == q) return root;
    TreeNode* left = lowestCommonAncestor(root->left, p, q);
    TreeNode* right = lowestCommonAncestor(root->right, p, q);
    if (left && right) return root;
    return left ? left : right;
}

bool isValidBSTImpl(TreeNode* node, long long low, long long high) {
    if (!node) return true;
    if (node->val <= low || node->val >= high) return false;
    return isValidBSTImpl(node->left, low, node->val) &&
           isValidBSTImpl(node->right, node->val, high);
}

bool isValidBST(TreeNode* root) {
    return isValidBSTImpl(root, std::numeric_limits<long long>::min(),
                          std::numeric_limits<long long>::max());
}

int numIslands(std::vector<std::vector<char>>& grid) {
    if (grid.empty() || grid[0].empty()) return 0;
    int m = static_cast<int>(grid.size());
    int n = static_cast<int>(grid[0].size());
    int ans = 0;
    const int dirs[5] = {1, 0, -1, 0, 1};
    std::function<void(int, int)> dfs = [&](int x, int y) {
        grid[x][y] = '0';
        for (int k = 0; k < 4; ++k) {
            int nx = x + dirs[k];
            int ny = y + dirs[k + 1];
            if (nx >= 0 && nx < m && ny >= 0 && ny < n && grid[nx][ny] == '1') {
                dfs(nx, ny);
            }
        }
    };
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j) {
            if (grid[i][j] == '1') {
                ++ans;
                dfs(i, j);
            }
        }
    }
    return ans;
}

std::vector<int> topologicalSort(int n, const std::vector<std::pair<int, int>>& edges) {
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

int lengthOfLIS(const std::vector<int>& nums) {
    std::vector<int> tails;
    for (int x : nums) {
        auto it = std::lower_bound(tails.begin(), tails.end(), x);
        if (it == tails.end()) tails.push_back(x);
        else *it = x;
    }
    return static_cast<int>(tails.size());
}

int longestCommonSubsequence(const std::string& a, const std::string& b) {
    int n = static_cast<int>(a.size());
    int m = static_cast<int>(b.size());
    std::vector<int> dp(m + 1, 0);
    for (int i = 1; i <= n; ++i) {
        int prev = 0;
        for (int j = 1; j <= m; ++j) {
            int old = dp[j];
            if (a[i - 1] == b[j - 1]) dp[j] = prev + 1;
            else dp[j] = std::max(dp[j], dp[j - 1]);
            prev = old;
        }
    }
    return dp[m];
}

int knapsack01(const std::vector<int>& weight, const std::vector<int>& value, int capacity) {
    std::vector<int> dp(capacity + 1, 0);
    for (size_t i = 0; i < weight.size(); ++i) {
        for (int c = capacity; c >= weight[i]; --c) {
            dp[c] = std::max(dp[c], dp[c - weight[i]] + value[i]);
        }
    }
    return dp[capacity];
}

#ifdef INTERVIEW_SNIPPETS_DEMO
int main() {
    LRUCache cache(2);
    cache.put(1, 10);
    cache.put(2, 20);
    std::cout << cache.get(1).value_or(-1) << "\n";

    ThreadPool pool(2);
    auto fut = pool.submit([](int a, int b) { return a + b; }, 1, 2);
    std::cout << fut.get() << "\n";
    return 0;
}
#endif
