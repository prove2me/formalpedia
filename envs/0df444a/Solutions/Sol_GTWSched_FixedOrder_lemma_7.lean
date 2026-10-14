-- Prove2me | solution 1 for GTWSched.FixedOrder.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:25:15.301837+00:00
-- url     : https://prove2.me/submissions/d3e3ed5c-c2ad-43b2-bdc0-0ce902732e77

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm



namespace GTWSched.FixedOrder

lemma foldl_min_aux (a s : ℕ → ℝ) (L : List ℕ) (d : ℝ) :
    L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d ≤ d ∧
    (∀ i ∈ L, a i < s i →
      L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d ≤ s i - a i) ∧
    (L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d = d ∨
      ∃ i ∈ L, a i < s i ∧
        L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d = s i - a i) := by
  induction L generalizing d with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons]
    by_cases hx : a x < s x
    · simp only [hx, if_true]
      obtain ⟨h1, h2, h3⟩ := ih (min d (s x - a x))
      refine ⟨h1.trans (min_le_left _ _), ?_, ?_⟩
      · intro i hi hai
        rcases List.mem_cons.mp hi with rfl | hi
        · exact h1.trans (min_le_right _ _)
        · exact h2 i hi hai
      · rcases h3 with h3 | ⟨i, hi, hai, h3⟩
        · rcases min_choice d (s x - a x) with h | h
          · left; rw [h3, h]
          · right; exact ⟨x, List.mem_cons_self, hx, by rw [h3, h]⟩
        · right; exact ⟨i, List.mem_cons_of_mem _ hi, hai, h3⟩
    · simp only [hx, if_false]
      obtain ⟨h1, h2, h3⟩ := ih d
      refine ⟨h1, ?_, ?_⟩
      · intro i hi hai
        rcases List.mem_cons.mp hi with rfl | hi
        · exact absurd hai hx
        · exact h2 i hi hai
      · rcases h3 with h3 | ⟨i, hi, hai, h3⟩
        · left; exact h3
        · right; exact ⟨i, List.mem_cons_of_mem _ hi, hai, h3⟩

lemma foldl_ge_aux (a s : ℕ → ℝ) (L : List ℕ) (d c : ℝ) (hd : c ≤ d)
    (h : ∀ i ∈ L, a i < s i → c ≤ s i - a i) :
    c ≤ L.foldl (fun d i => if a i < s i then min d (s i - a i) else d) d := by
  induction L generalizing d with
  | nil => simpa using hd
  | cons x L ih =>
    simp only [List.foldl_cons]
    apply ih
    · by_cases hx : a x < s x
      · simp only [hx, if_true]
        exact le_min hd (h x List.mem_cons_self hx)
      · simp only [hx, if_false]; exact hd
    · intro i hi; exact h i (List.mem_cons_of_mem _ hi)

lemma shiftAmount_le (a l s : ℕ → ℝ) (j m : ℕ) :
    shiftAmount a l s j m ≤ s j - prevEnd l s j ∧
    (∀ i, j ≤ i → i ≤ m → a i < s i → shiftAmount a l s j m ≤ s i - a i) := by
  obtain ⟨h1, h2, -⟩ := foldl_min_aux a s (Finset.Icc j m).toList (s j - prevEnd l s j)
  refine ⟨h1, fun i hji him hai => h2 i ?_ hai⟩
  simp [Finset.mem_Icc, hji, him]

lemma shiftAmount_cases (a l s : ℕ → ℝ) (j m : ℕ) :
    shiftAmount a l s j m = s j - prevEnd l s j ∨
    ∃ i, j ≤ i ∧ i ≤ m ∧ a i < s i ∧ shiftAmount a l s j m = s i - a i := by
  obtain ⟨-, -, h3⟩ := foldl_min_aux a s (Finset.Icc j m).toList (s j - prevEnd l s j)
  rcases h3 with h | ⟨i, hi, hai, h⟩
  · left; exact h
  · right
    simp only [Finset.mem_toList, Finset.mem_Icc] at hi
    exact ⟨i, hi.1, hi.2, hai, h⟩

lemma shiftAmount_ge (a l s : ℕ → ℝ) (j m : ℕ) (c : ℝ) (h1 : c ≤ s j - prevEnd l s j)
    (h2 : ∀ i, j ≤ i → i ≤ m → a i < s i → c ≤ s i - a i) :
    c ≤ shiftAmount a l s j m := by
  apply foldl_ge_aux a s _ _ c h1
  intro i hi hai
  simp only [Finset.mem_toList, Finset.mem_Icc] at hi
  exact h2 i hi.1 hi.2 hai

lemma shift_cost_core (a l s : ℕ → ℝ) (m j : ℕ) (δ : ℝ)
    (hbalance : decCount a s j m = incCount a s j m)
    (hδ : 0 ≤ δ ∧ δ ≤ shiftAmount a l s j m) :
    cost a (m + 1) (shiftRange s j m δ) = cost a (m + 1) s := by
  obtain ⟨h0, h1⟩ := hδ
  have hle := (shiftAmount_le a l s j m).2
  unfold cost
  have key : ∀ i ∈ Finset.range (m+1), |shiftRange s j m δ i - a i| =
      |s i - a i| + (if j ≤ i ∧ i ≤ m then (if a i < s i then -δ else δ) else 0) := by
    intro i hi
    by_cases hij : j ≤ i ∧ i ≤ m
    · simp only [shiftRange, hij, and_self, if_true]
      by_cases hai : a i < s i
      · have := hle i hij.1 hij.2 hai
        simp only [hai, if_true]
        rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]; ring
      · have hai' : s i ≤ a i := not_lt.mp hai
        simp only [hai, if_false]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
    · simp [shiftRange, hij]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have : ∑ i ∈ Finset.range (m+1), (if j ≤ i ∧ i ≤ m then (if a i < s i then -δ else δ) else (0:ℝ)) = 0 := by
    rw [← Finset.sum_filter]
    have hf : (Finset.range (m+1)).filter (fun i => j ≤ i ∧ i ≤ m) = Finset.Icc j m := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [hf, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have : (Finset.Icc j m).filter (fun i => ¬ a i < s i) = (Finset.Icc j m).filter (fun i => s i ≤ a i) := by
      ext i; simp
    rw [this]
    unfold decCount incCount at hbalance
    rw [hbalance]; simp
  rw [this, add_zero]


noncomputable def cs (a s : ℕ → ℝ) (i : ℕ) : ℤ := if a i < s i then -1 else 1

noncomputable def net (a s : ℕ → ℝ) (j k : ℕ) : ℤ := ∑ i ∈ Finset.Ico j (k + 1), cs a s i

def ChainP (l s : ℕ → ℝ) (j k : ℕ) : Prop := ∀ i, j ≤ i → i < k → s i + l i = s (i + 1)

def StartP (l s : ℕ → ℝ) (j : ℕ) : Prop := j = 0 ∨ s (j - 1) + l (j - 1) < s j

lemma net_eq (a s : ℕ → ℝ) (j k : ℕ) :
    net a s j k = (incCount a s j k : ℤ) - (decCount a s j k : ℤ) := by
  unfold net cs incCount decCount
  rw [Finset.Ico_add_one_right_eq_Icc, Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul]
  have : (Finset.Icc j k).filter (fun i => ¬ a i < s i) = (Finset.Icc j k).filter (fun i => s i ≤ a i) := by
    ext i; simp
  rw [this]
  simp
  ring

lemma cs_of_lt {a s : ℕ → ℝ} {i : ℕ} (h : a i < s i) : cs a s i = -1 := by simp [cs, h]
lemma cs_of_le {a s : ℕ → ℝ} {i : ℕ} (h : s i ≤ a i) : cs a s i = 1 := by
  simp [cs, not_lt.mpr h]

lemma net_congr {a s t : ℕ → ℝ} {j k : ℕ} (h : ∀ i, j ≤ i → i ≤ k → t i = s i) :
    net a t j k = net a s j k := by
  unfold net
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Ico] at hi
  unfold cs
  rw [h i hi.1 (by omega)]

lemma net_succ (a s : ℕ → ℝ) {j k : ℕ} (h : j ≤ k + 1) :
    net a s j (k + 1) = net a s j k + cs a s (k + 1) := by
  unfold net
  rw [Finset.sum_Ico_succ_top (by omega : j ≤ k + 1 + 0)]

lemma net_split (a s : ℕ → ℝ) {j m k : ℕ} (h1 : j ≤ m + 1) (h2 : m ≤ k) :
    net a s j k = net a s j m + net a s (m + 1) k := by
  unfold net
  rw [Finset.sum_Ico_consecutive _ h1 (by omega : m + 1 ≤ k + 1)]

lemma net_mono {a s t : ℕ → ℝ} {j k : ℕ} (h : ∀ i, j ≤ i → i ≤ k → cs a s i ≤ cs a t i) :
    net a s j k ≤ net a t j k := by
  unfold net
  apply Finset.sum_le_sum
  intro i hi
  simp only [Finset.mem_Ico] at hi
  exact h i hi.1 (by omega)

lemma net_lt {a s t : ℕ → ℝ} {j k i0 : ℕ} (h : ∀ i, j ≤ i → i ≤ k → cs a s i ≤ cs a t i)
    (hi0 : j ≤ i0) (hk : i0 ≤ k) (hlt : cs a s i0 < cs a t i0) :
    net a s j k < net a t j k := by
  unfold net
  apply Finset.sum_lt_sum
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    exact h i hi.1 (by omega)
  · exact ⟨i0, by simp only [Finset.mem_Ico]; omega, hlt⟩

lemma net_single (a s : ℕ → ℝ) (j : ℕ) : net a s j j = cs a s j := by
  unfold net; simp

/-! blockStart -/

lemma bs_le (l s : ℕ → ℝ) (m : ℕ) : blockStart l s m ≤ m := by
  induction m with
  | zero => simp [blockStart]
  | succ m ih =>
    unfold blockStart
    split_ifs
    · omega
    · exact le_rfl

lemma bs_chain (l s : ℕ → ℝ) (m : ℕ) :
    ∀ i, blockStart l s m ≤ i → i < m → s i + l i = s (i + 1) := by
  induction m with
  | zero => intro i _ h; omega
  | succ m ih =>
    intro i hi him
    unfold blockStart at hi
    split_ifs at hi with h
    · rcases Nat.lt_succ_iff_lt_or_eq.mp him with h' | h'
      · exact ih i hi h'
      · subst h'; exact h
    · omega

lemma bs_start (l s : ℕ → ℝ) (m : ℕ) :
    blockStart l s m = 0 ∨ s (blockStart l s m - 1) + l (blockStart l s m - 1) ≠ s (blockStart l s m) := by
  induction m with
  | zero => left; simp [blockStart]
  | succ m ih =>
    by_cases h : s m + l m = s (m + 1)
    · have : blockStart l s (m + 1) = blockStart l s m := by simp [blockStart, h]
      rw [this]; exact ih
    · have : blockStart l s (m + 1) = m + 1 := by simp [blockStart, h]
      rw [this]; right; simpa using h

lemma bs_unique (l s : ℕ → ℝ) (m j : ℕ) (hj : j ≤ m) (hc : ChainP l s j m)
    (hs : j = 0 ∨ s (j - 1) + l (j - 1) ≠ s j) : blockStart l s m = j := by
  induction m with
  | zero => have : j = 0 := by omega
            subst this; simp [blockStart]
  | succ m ih =>
    by_cases h : s m + l m = s (m + 1)
    · have e : blockStart l s (m + 1) = blockStart l s m := by simp [blockStart, h]
      rw [e]
      by_cases hjm : j = m + 1
      · subst hjm
        rcases hs with hs | hs
        · omega
        · exact absurd (by simpa using h) hs
      · exact ih (by omega) (fun i hi him => hc i hi (by omega))
    · have e : blockStart l s (m + 1) = m + 1 := by simp [blockStart, h]
      rw [e]
      by_contra hne
      exact h (hc m (by omega) (by omega))

/-! place / shiftRange -/

lemma cost_place (a s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    cost a (n + 1) (place s n x) = cost a n s + |x - a n| := by
  unfold cost
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have : i ≠ n := by simp at hi; omega
    simp [place, this]
  · simp [place]

def Inv (a l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop :=
  ∀ j k, j ≤ k → k < n → StartP l s j → ChainP l s j k →
    s j = 0 ∨ (0 ≤ net a s j k ∧ ((k + 1 = n ∨ s k + l k < s (k + 1)) → 0 < net a s j k))

def Good (a l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop := FixedFeasible l n s ∧ Inv a l n s

lemma good_zero (a l : ℕ → ℝ) (s : ℕ → ℝ) : Good a l 0 s := by
  refine ⟨⟨fun i hi => by omega, fun i hi => by omega⟩, fun j k _ hk => by omega⟩

lemma place_lt (s : ℕ → ℝ) (n : ℕ) (x : ℝ) {i : ℕ} (h : i < n) : place s n x i = s i := by
  simp [place, Nat.ne_of_lt h]

lemma partA (a l : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) (x : ℝ) (hg : Good a l n s)
    (hx0 : 0 ≤ x) (hxa : x ≤ a n) (hprev : 0 < n → s (n - 1) + l (n - 1) ≤ x) :
    Good a l (n + 1) (place s n x) := by
  obtain ⟨⟨hf0, hf1⟩, hinv⟩ := hg
  have hpn : place s n x n = x := by simp [place]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases h : i < n
    · rw [place_lt s n x h]; exact hf0 i h
    · have : i = n := by omega
      subst this; rw [hpn]; exact hx0
  · intro i hi
    by_cases h : i + 1 < n
    · rw [place_lt s n x h, place_lt s n x (by omega)]; exact hf1 i h
    · have : i + 1 = n := by omega
      rw [place_lt s n x (by omega), this, hpn]
      have := hprev (by omega)
      have e : n - 1 = i := by omega
      rw [e] at this; exact this
  · intro j k hjk hk hS hC
    by_cases hkn : k < n
    · have hS' : StartP l s j := by
        rcases hS with h | h
        · exact Or.inl h
        · right
          rwa [place_lt s n x (by omega), place_lt s n x (by omega)] at h
      have hC' : ChainP l s j k := by
        intro i hi hik
        have := hC i hi hik
        rwa [place_lt s n x (show i < n by omega), place_lt s n x (show i + 1 < n by omega)] at this
      rcases hinv j k hjk hkn hS' hC' with h | ⟨h1, h2⟩
      · left; rwa [place_lt s n x (by omega)]
      · right
        have hnet : net a (place s n x) j k = net a s j k :=
          net_congr (fun i _ hik => place_lt s n x (by omega))
        rw [hnet]
        refine ⟨h1, fun hg => h2 ?_⟩
        rcases hg with hg | hg
        · omega
        · by_cases hk1 : k + 1 = n
          · exact Or.inl hk1
          · right
            rwa [place_lt s n x hkn, place_lt s n x (show k + 1 < n by omega)] at hg
    · have hkn' : k = n := by omega
      subst hkn'
      by_cases hjk' : j = k
      · subst hjk'
        right
        have : cs a (place s j x) j = 1 := cs_of_le (by rw [hpn]; exact hxa)
        rw [net_single, this]; exact ⟨by norm_num, fun _ => by norm_num⟩
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        have hS' : StartP l s j := by
          rcases hS with h | h
          · exact Or.inl h
          · right
            rwa [place_lt s (m+1) x (by omega), place_lt s (m+1) x (by omega)] at h
        have hC' : ChainP l s j m := by
          intro i hi him
          have := hC i hi (by omega)
          rwa [place_lt s (m+1) x (by omega), place_lt s (m+1) x (by omega)] at this
        rcases hinv j m (by omega) (by omega) hS' hC' with h | ⟨h1, h2⟩
        · left; rwa [place_lt s (m+1) x (by omega)]
        · right
          have h3 := h2 (Or.inl rfl)
          have hnet : net a (place s (m+1) x) j m = net a s j m :=
            net_congr (fun i _ hik => place_lt s (m+1) x (by omega))
          have hc : cs a (place s (m+1) x) (m+1) = 1 := cs_of_le (by rw [hpn]; exact hxa)
          rw [net_succ a _ (by omega), hnet, hc]
          exact ⟨by omega, fun _ => by omega⟩

lemma cs_mono_shift (a r t : ℕ → ℝ) (i : ℕ) (h : t i ≤ r i) : cs a r i ≤ cs a t i := by
  by_cases hi : a i < r i
  · rw [cs_of_lt hi]; unfold cs; split_ifs <;> norm_num
  · rw [cs_of_le (not_lt.mp hi), cs_of_le (h.trans (not_lt.mp hi))]

lemma lb_basic (a l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (n : ℕ) (hn : 0 < n) (s : ℕ → ℝ)
    (hg : Good a l n s) (hlate : a n < s (n - 1) + l (n - 1))
    (r : ℕ → ℝ) (hr : r = place s n (s (n - 1) + l (n - 1)))
    (j : ℕ) (hj : j = blockStart l r n) :
    j < n ∧ (∀ i, i < n → r i = s i) ∧ r n = s (n - 1) + l (n - 1) ∧
    (j = 0 ∨ s (j - 1) + l (j - 1) < s j) ∧ ChainP l s j (n - 1) ∧ ChainP l r j n ∧
    prevEnd l r j ≤ r j ∧ 0 ≤ prevEnd l r j ∧
    (r j ≠ 0 → 0 < net a s j (n - 1) ∧ ∀ k, j ≤ k → k ≤ n → 0 ≤ net a r j k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨hf0, hf1⟩, hinv⟩ := hg
  simp only [Nat.add_sub_cancel] at hlate ⊢
  have hrlt : ∀ i, i < m + 1 → r i = s i := fun i hi => by rw [hr]; exact place_lt s _ _ hi
  have hrn : r (m + 1) = s m + l m := by rw [hr]; simp [place]
  have hchR : ChainP l r j (m + 1) := by rw [hj]; exact bs_chain l r (m + 1)
  have hjle : j ≤ m + 1 := by rw [hj]; exact bs_le l r (m + 1)
  have hjn : j < m + 1 := by
    rcases Nat.lt_or_ge j (m + 1) with h | h
    · exact h
    · exfalso
      have : j = m + 1 := by omega
      have hst := bs_start l r (m + 1)
      rw [← hj] at hst
      rcases hst with h0 | h0
      · omega
      · apply h0
        rw [this]; simp only [Nat.add_sub_cancel]
        rw [hrlt m (by omega), hrn]
  have hStartS : j = 0 ∨ s (j - 1) + l (j - 1) < s j := by
    have hst := bs_start l r (m + 1)
    rw [← hj] at hst
    rcases hst with h0 | h0
    · exact Or.inl h0
    · by_cases hj0 : j = 0
      · exact Or.inl hj0
      right
      rw [hrlt (j - 1) (by omega), hrlt j hjn] at h0
      exact lt_of_le_of_ne (by
        have := hf1 (j - 1) (by omega)
        have e : j - 1 + 1 = j := by omega
        rwa [e] at this) h0
  have hChainS : ChainP l s j m := by
    intro i hi him
    have := hchR i hi (by omega)
    rwa [hrlt i (by omega), hrlt (i + 1) (by omega)] at this
  have hpe0 : 0 ≤ prevEnd l r j := by
    unfold prevEnd
    split_ifs with h
    · exact le_rfl
    · rw [hrlt (j - 1) (by omega)]
      exact add_nonneg (hf0 _ (by omega)) (hl _)
  have hpe : prevEnd l r j ≤ r j := by
    unfold prevEnd
    split_ifs with h
    · rw [hrlt j hjn]; exact hf0 _ hjn
    · rcases hStartS with h' | h'
      · exact absurd h' h
      · rw [hrlt (j - 1) (by omega), hrlt j hjn]; exact h'.le
  refine ⟨hjn, hrlt, hrn, hStartS, hChainS, hchR, hpe, hpe0, ?_⟩
  intro hrj
  have hsj : s j ≠ 0 := by rw [← hrlt j hjn]; exact hrj
  have hstart' : StartP l s j := hStartS
  rcases hinv j m (by omega) (by omega) hstart' hChainS with h | ⟨h1, h2⟩
  · exact absurd h hsj
  · have hpos := h2 (Or.inl rfl)
    refine ⟨hpos, ?_⟩
    intro k hjk hkn
    by_cases hk : k ≤ m
    · have hC2 : ChainP l s j k := fun i hi hik => hChainS i hi (by omega)
      rcases hinv j k hjk (by omega) hstart' hC2 with h | ⟨h1', _⟩
      · exact absurd h hsj
      · rw [net_congr (fun i _ hik => hrlt i (by omega))]; exact h1'
    · have : k = m + 1 := by omega
      subst this
      have hc : cs a r (m + 1) = -1 := cs_of_lt (by rw [hrn]; exact hlate)
      rw [net_succ a _ (by omega), hc, net_congr (fun i _ hik => hrlt i (by omega))]
      omega

lemma partB (a l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (n : ℕ) (hn : 0 < n) (s : ℕ → ℝ)
    (hg : Good a l n s) (hlate : a n < s (n - 1) + l (n - 1))
    (r : ℕ → ℝ) (hr : r = place s n (s (n - 1) + l (n - 1)))
    (j : ℕ) (hj : j = blockStart l r n) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ r j - prevEnd l r j)
    (hδ3 : (δ = 0 ∧ (r j = 0 ∨ net a r j n ≠ 0)) ∨
       (net a r j n = 0 ∧ r j ≠ 0 ∧ (δ = r j - prevEnd l r j ∨
          ∃ i, j ≤ i ∧ i ≤ n ∧ a i < r i ∧ δ = r i - a i))) :
    Good a l (n + 1) (shiftRange r j n δ) := by
  obtain ⟨hjn, hrlt, hrn, hStartS, hChainS, hChainR, hpe_le, hpe0, hpref⟩ :=
    lb_basic a l hl n hn s hg hlate r hr j hj
  obtain ⟨⟨hf0, hf1⟩, hinv⟩ := hg
  obtain ⟨t, ht⟩ : ∃ t, t = shiftRange r j n δ := ⟨_, rfl⟩
  rw [← ht]
  have hin : ∀ i, j ≤ i → i ≤ n → t i = r i - δ := by
    intro i h1 h2; rw [ht]; simp [shiftRange, h1, h2]
  have hout : ∀ i, i < j → t i = s i := by
    intro i hi; rw [ht]
    have : ¬ (j ≤ i ∧ i ≤ n) := by omega
    simp only [shiftRange, this, if_false]; exact hrlt i (by omega)
  have hle : ∀ i, i ≤ n → t i ≤ r i := by
    intro i hi
    by_cases h : j ≤ i
    · rw [hin i h hi]; linarith
    · rw [hout i (by omega), hrlt i (by omega)]
  have hK2 : ∀ i, j ≤ i → i < n → t i + l i = t (i + 1) := by
    intro i h1 h2
    rw [hin i h1 (by omega), hin (i + 1) (by omega) (by omega)]
    have := hChainR i h1 h2
    linarith
  have hmono : ∀ i, j ≤ i → i ≤ n → t j ≤ t i := by
    intro i h1 h2
    induction i, h1 using Nat.le_induction with
    | base => exact le_rfl
    | succ i hi ih =>
      have := hK2 i hi (by omega)
      have := hl i
      have := ih (by omega)
      linarith
  have htj : prevEnd l r j ≤ t j := by
    rw [hin j le_rfl (by omega)]; linarith
  have hrj0 : r j = 0 → δ = 0 := by
    intro h
    have : δ ≤ r j := by linarith
    linarith
  have hrj_s : r j = s j := hrlt j hjn
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases h : i < j
    · rw [hout i h]; exact hf0 i (by omega)
    · have := hmono i (by omega) (by omega)
      linarith
  · intro i hi
    by_cases h1 : i + 1 < j
    · rw [hout i (by omega), hout (i + 1) h1]; exact hf1 i (by omega)
    · by_cases h2 : i + 1 = j
      · rw [hout i (by omega), hin (i + 1) (by omega) (by omega), h2]
        have hj0 : j ≠ 0 := by omega
        have : prevEnd l r j = r (j - 1) + l (j - 1) := by simp [prevEnd, hj0]
        have e : j - 1 = i := by omega
        rw [this, e, hrlt i (by omega)] at hδ1
        linarith
      · rw [hK2 i (by omega) (by omega)]
  · intro j' k hjk hk hS hC
    have hcsmono : ∀ i, j ≤ i → i ≤ n → cs a r i ≤ cs a t i :=
      fun i _ hi => cs_mono_shift a r t i (hle i hi)
    by_cases hkj : k < j
    · -- block entirely before j
      have hS' : StartP l s j' := by
        rcases hS with h | h
        · exact Or.inl h
        · right
          rwa [hout (j' - 1) (by omega), hout j' (by omega)] at h
      have hC' : ChainP l s j' k := by
        intro i hi hik
        have := hC i hi hik
        rwa [hout i (by omega), hout (i + 1) (by omega)] at this
      rcases hinv j' k hjk (by omega) hS' hC' with h | ⟨h1, h2⟩
      · left; rwa [hout j' (by omega)]
      · right
        have hnet : net a t j' k = net a s j' k :=
          net_congr (fun i _ hik => hout i (by omega))
        rw [hnet]
        refine ⟨h1, fun hg => h2 ?_⟩
        rcases hg with hg | hg
        · omega
        · right
          rw [hout k hkj] at hg
          have h3 : t (k + 1) ≤ s (k + 1) := by
            have := hle (k + 1) (by omega)
            rwa [hrlt (k + 1) (by omega)] at this
          linarith
    · -- block reaches into [j, n]
      have hjj : j' ≤ j := by
        by_contra hcon
        have hj'0 : j' ≠ 0 := by omega
        rcases hS with h | h
        · exact hj'0 h
        · have := hK2 (j' - 1) (by omega) (by omega)
          have e : j' - 1 + 1 = j' := by omega
          rw [e] at this
          linarith
      -- gap after k is impossible unless k = n
      have hkn : (k + 1 = n + 1 ∨ t k + l k < t (k + 1)) → k = n := by
        intro hg
        rcases hg with hg | hg
        · omega
        · by_contra hne
          have := hK2 k (by omega) (by omega)
          linarith
      rcases Nat.lt_or_ge j' j with hlt | hge
      · -- merged with the previous block
        have hj0 : 0 < j := by omega
        have hS' : StartP l s j' := by
          rcases hS with h | h
          · exact Or.inl h
          · right
            rwa [hout (j' - 1) (by omega), hout j' (by omega)] at h
        have hC' : ChainP l s j' (j - 1) := by
          intro i hi hik
          have := hC i hi (by omega)
          rwa [hout i (by omega), hout (i + 1) (by omega)] at this
        have hgap : s (j - 1) + l (j - 1) < s j := by
          rcases hStartS with h | h
          · omega
          · exact h
        rcases hinv j' (j - 1) (by omega) (by omega) hS' hC' with h | ⟨h1, h2⟩
        · left; rwa [hout j' (by omega)]
        · right
          have e : j - 1 + 1 = j := by omega
          have hpos : 0 < net a s j' (j - 1) := by
            apply h2; right; rwa [e]
          have hsplit := net_split a t (j := j') (m := j - 1) (k := k) (by omega) (by omega)
          rw [e] at hsplit
          have hnet : net a t j' (j - 1) = net a s j' (j - 1) :=
            net_congr (fun i _ hik => hout i (by omega))
          have hrj : r j ≠ 0 := by
            rw [hrj_s]
            have := hf0 (j - 1) (by omega)
            have := hl (j - 1)
            intro h0
            linarith
          have h4 := (hpref hrj).2 k (by omega) (by omega)
          have h5 : net a r j k ≤ net a t j k :=
            net_mono (fun i hi1 hi2 => hcsmono i hi1 (by omega))
          have h6 : 0 < net a t j' k := by rw [hsplit, hnet]; omega
          exact ⟨h6.le, fun _ => h6⟩
      · -- j' = j
        have hjj' : j' = j := le_antisymm hjj hge
        subst hjj'
        by_cases hrj : r j' = 0
        · left; rw [hin j' le_rfl (by omega), hrj0 hrj, hrj]; ring
        · have hp := (hpref hrj).2
          have hnn : ∀ k', j' ≤ k' → k' ≤ n → 0 ≤ net a t j' k' := by
            intro k' h1 h2
            have h5 : net a r j' k' ≤ net a t j' k' :=
              net_mono (fun i hi1 hi2 => hcsmono i hi1 (by omega))
            have := hp k' h1 h2
            omega
          have hkey : t j' = 0 ∨ 0 < net a t j' n := by
            have h5 : net a r j' n ≤ net a t j' n :=
              net_mono (fun i hi1 hi2 => hcsmono i hi1 hi2)
            have h6 := hp n (by omega) le_rfl
            rcases hδ3 with ⟨hd0, hd1⟩ | ⟨hnr, _, hE⟩
            · right
              rcases hd1 with h | h
              · exact absurd h hrj
              · omega
            · rcases hE with hE | ⟨i, hi1, hi2, hi3, hi4⟩
              · by_cases hj0 : j' = 0
                · left
                  rw [hin j' le_rfl (by omega), hE]
                  simp [prevEnd, hj0]
                · exfalso
                  rcases hS with h | h
                  · exact hj0 h
                  · rw [hout (j' - 1) (by omega), ← hrlt (j' - 1) (by omega), hin j' le_rfl (by omega), hE] at h
                    have : prevEnd l r j' = r (j' - 1) + l (j' - 1) := by simp [prevEnd, hj0]
                    linarith
              · right
                have hti : t i = a i := by rw [hin i hi1 hi2]; linarith
                have h7 : net a r j' n < net a t j' n :=
                  net_lt (i0 := i) (fun i' hi1' hi2' => hcsmono i' hi1' hi2') hi1 hi2
                    (by rw [cs_of_lt hi3, cs_of_le (le_of_eq hti)]; norm_num)
                omega
          rcases hkey with hk0 | hk1
          · left; exact hk0
          · right
            refine ⟨hnn k (by omega) (by omega), fun hg => ?_⟩
            have := hkn hg
            subst this
            exact hk1

lemma shiftRange_zero (r : ℕ → ℝ) (j n : ℕ) : shiftRange r j n 0 = r := by
  funext i; simp [shiftRange]

lemma good_step (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (n : ℕ) (s : ℕ → ℝ)
    (hg : Good a l n s) : Good a l (n + 1) (step a l n s) := by
  unfold step
  by_cases hn : n = 0
  · subst hn
    simp only [if_true]
    exact partA a l 0 s (a 0) hg (ha 0) le_rfl (fun h => absurd h (lt_irrefl 0))
  · simp only [hn, if_false]
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hf : s (n - 1) + l (n - 1) ≤ a n
    · simp only [hf, if_true]
      exact partA a l n s (a n) hg (ha n) le_rfl (fun _ => hf)
    · simp only [hf, if_false]
      have hlate : a n < s (n - 1) + l (n - 1) := not_le.mp hf
      obtain ⟨r, hr⟩ : ∃ r, r = place s n (s (n - 1) + l (n - 1)) := ⟨_, rfl⟩
      rw [← hr]
      obtain ⟨j, hj⟩ : ∃ j, j = blockStart l r n := ⟨_, rfl⟩
      rw [← hj]
      obtain ⟨hjn, hrlt, hrn, hStartS, hChainS, hChainR, hpe_le, hpe0, hpref⟩ :=
        lb_basic a l hl n hn0 s hg hlate r hr j hj
      split_ifs with hcond
      · have hd0 : 0 ≤ shiftAmount a l r j n :=
          shiftAmount_ge a l r j n 0 (by linarith) (fun i _ _ h => by linarith)
        have hd1 := (shiftAmount_le a l r j n).1
        have hnet : net a r j n = 0 := by
          rw [net_eq, hcond.1]; ring
        refine partB a l hl n hn0 s hg hlate r hr j hj _ hd0 hd1 (Or.inr ⟨hnet, hcond.2, ?_⟩)
        rcases shiftAmount_cases a l r j n with h | ⟨i, h1, h2, h3, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨i, h1, h2, h3, h4⟩
      · have := partB a l hl n hn0 s hg hlate r hr j hj 0 le_rfl (by linarith) (Or.inl ⟨rfl, ?_⟩)
        · rwa [shiftRange_zero] at this
        · by_cases hrj : r j = 0
          · exact Or.inl hrj
          · right
            rw [net_eq]
            intro h
            apply hcond
            refine ⟨?_, hrj⟩
            omega

lemma sched_good (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (n : ℕ) :
    Good a l n (sched a l n) := by
  induction n with
  | zero => exact good_zero a l _
  | succ n ih => exact good_step a l ha hl n _ ih

theorem lemma_7_core (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n j k : ℕ) (hblock : IsBlock l n (sched a l n) j k) :
    decCount a (sched a l n) j k < incCount a (sched a l n) j k ∨
      sched a l n j = 0 := by
  obtain ⟨hjk, hkn, hch, hst, hend⟩ := hblock
  obtain ⟨-, hinv⟩ := sched_good a l ha hl n
  rcases hinv j k hjk hkn hst hch with h | ⟨h1, h2⟩
  · exact Or.inr h
  · left
    have := h2 (by rcases hend with h | h; exact Or.inl h; exact Or.inr h)
    rw [net_eq] at this
    omega

end GTWSched.FixedOrder

open GTWSched.FixedOrder


theorem solution (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n j k : ℕ) (hblock : IsBlock l n (sched a l n) j k) :
    decCount a (sched a l n) j k < incCount a (sched a l n) j k ∨
      sched a l n j = 0 := by
  exact lemma_7_core a l ha hl n j k hblock
