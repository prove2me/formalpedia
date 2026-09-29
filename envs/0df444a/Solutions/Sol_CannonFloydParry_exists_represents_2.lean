-- Prove2me | solution 2 for CannonFloydParry.exists_represents
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-22T14:19:50.799222+00:00
-- url     : https://prove2.me/submissions/08f4c654-b2c5-47b4-9b2c-9eaa827d6283

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Theorems.Thm_CannonFloydParry_isStandardDyadicPartition_marks

/-!
# Dyadic piecewise-linear machinery for Cannon–Floyd–Parry Lemma 4.2

Shared development, kept as its own file while it is being built.  It is concatenated into the
self-contained solution files that are submitted to the platform.

Two independent parts:

* `SumPow` — the arithmetic core: a positive integer `q` is a sum of *exactly* `k` integer
  powers of two whenever `q < 2 ^ k`.
* the piecewise-linear constructor — from strictly monotone dyadic breakpoint data `s` and
  target data `t` whose consecutive gaps have power-of-two ratios, an order isomorphism of `ℝ`
  that is the identity off `[0,1]` and carries `s j` to `t j`.
-/

open CannonFloydParry

namespace CFPLib

/-! ### Sums of exactly `k` powers of two -/

/-- `SumPow k q`: the real number `q` is a sum of exactly `k` integer powers of two. -/
def SumPow (k : ℕ) (q : ℝ) : Prop :=
  ∃ l : List ℤ, l.length = k ∧ (l.map fun e => (2 : ℝ) ^ e).sum = q

lemma two_ne_zero' : (2 : ℝ) ≠ 0 := by norm_num

lemma SumPow.one (e : ℤ) : SumPow 1 ((2 : ℝ) ^ e) := ⟨[e], rfl, by simp⟩

lemma SumPow.cons {k : ℕ} {q : ℝ} (e : ℤ) (h : SumPow k q) :
    SumPow (k + 1) ((2 : ℝ) ^ e + q) := by
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨e :: l, by simp [hl], by simp [hs]⟩

lemma halves (e : ℤ) : (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ e := by
  have h : (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (e - 1) := by
    rw [zpow_one]; ring
  rw [h, ← zpow_add₀ two_ne_zero']
  congr 1
  ring

/-- Splitting one summand in half increases the number of summands by one. -/
lemma SumPow.split {k : ℕ} {q : ℝ} (h : SumPow k q) (hk : 1 ≤ k) : SumPow (k + 1) q := by
  obtain ⟨l, hl, hs⟩ := h
  cases l with
  | nil => simp at hl; omega
  | cons e rest =>
      refine ⟨(e - 1) :: (e - 1) :: rest, by simpa using hl, ?_⟩
      simp only [List.map_cons, List.sum_cons] at hs ⊢
      rw [← add_assoc, halves, hs]

lemma SumPow.le {k m : ℕ} {q : ℝ} (h : SumPow k q) (hk : 1 ≤ k) (hm : k ≤ m) : SumPow m q := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · exact (ih (by omega)).split (by omega)
      · have : k = m + 1 := by omega
        exact this ▸ h

lemma sumPow_zpow {m : ℕ} (hm : 1 ≤ m) (e : ℤ) : SumPow m ((2 : ℝ) ^ e) :=
  (SumPow.one e).le le_rfl hm

/-- A positive integer is a sum of exactly `k` integer powers of two as soon as `q < 2 ^ k`. -/
lemma sumPow_nat : ∀ (k q : ℕ), 1 ≤ q → q < 2 ^ k → SumPow k (q : ℝ) := by
  intro k
  induction k with
  | zero => intro q h1 h2; simp at h2; omega
  | succ k ih =>
      intro q h1 h2
      rcases Nat.lt_or_ge q (2 ^ k) with hlt | hge
      · have hk : 1 ≤ k := by
          by_contra hc
          have : k = 0 := by omega
          subst this
          simp at hlt
          omega
        exact (ih q h1 hlt).split hk
      · set r := q - 2 ^ k with hr
        have hqr : (q : ℝ) = (2 : ℝ) ^ (k : ℤ) + (r : ℝ) := by
          have hq : q = 2 ^ k + r := by omega
          rw [hq]
          push_cast
          rw [zpow_natCast]
        have hrlt : r < 2 ^ k := by
          have h3 : q < 2 ^ (k + 1) := h2
          have h4 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · have hq2 : (q : ℝ) = (2 : ℝ) ^ (k : ℤ) := by rw [hqr, hr0]; simp
          rw [hq2]
          exact sumPow_zpow (by omega) _
        · rw [hqr]
          exact SumPow.cons _ (ih r hrpos hrlt)

/-! ### Dyadic arithmetic -/

lemma isDyadic_zero : IsDyadic (0 : ℝ) := ⟨0, 0, by norm_num⟩

lemma isDyadic_add {u v : ℝ} (hu : IsDyadic u) (hv : IsDyadic v) : IsDyadic (u + v) := by
  obtain ⟨m, k, rfl⟩ := hu
  obtain ⟨m', k', rfl⟩ := hv
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_zpow (a : ℤ) : IsDyadic ((2 : ℝ) ^ a) := by
  rcases le_or_gt 0 a with h | h
  · refine ⟨2 ^ a.toNat, 0, ?_⟩
    have h1 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h
    push_cast
    rw [pow_zero, div_one, ← zpow_natCast, h1]
  · refine ⟨1, (-a).toNat, ?_⟩
    have h1 : (((-a).toNat : ℕ) : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    push_cast
    rw [eq_div_iff (by positivity), ← zpow_natCast (2 : ℝ) ((-a).toNat), ← zpow_add₀ two_ne_zero',
      h1]
    simp

lemma isDyadic_natDiv (j M : ℕ) : IsDyadic ((j : ℝ) * (2 : ℝ) ^ (-(M : ℤ))) := by
  refine ⟨j, M, ?_⟩
  rw [zpow_neg, ← zpow_natCast (2 : ℝ) M]
  field_simp
  norm_cast

/-- A scaled sum of powers of two is dyadic. -/
lemma isDyadic_scaled_sum (l : List ℤ) (M : ℕ) :
    IsDyadic (((l.map fun e => (2 : ℝ) ^ e).sum) * (2 : ℝ) ^ (-(M : ℤ))) := by
  induction l with
  | nil => simpa using isDyadic_zero
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      refine isDyadic_add ?_ ih
      rw [← zpow_add₀ two_ne_zero']
      exact isDyadic_zpow _

/-! ### Assembling the exponent list -/

/-- A list all of whose entries vanish reads off as `0` at every index. -/
lemma getD_eq_zero_of_all {l : List ℤ} (h : ∀ e ∈ l, e = 0) (j : ℕ) : l.getD j 0 = 0 := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.getD_eq_getElem l 0 hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default l 0 hj]

/-- One gap's worth of exponents: the all-zero list when the gap keeps its length, and a
representation of the target length as a sum of powers of two otherwise. -/
lemma exists_block (k q : ℕ) (hq : 1 ≤ q) (hlt : q < 2 ^ k) :
    ∃ l : List ℤ, l.length = k ∧ (l.map fun e => (2 : ℝ) ^ e).sum = (q : ℝ) ∧
      (k = q → ∀ e ∈ l, e = 0) := by
  by_cases hkq : k = q
  · refine ⟨List.replicate k 0, by simp, ?_, fun _ e he => List.eq_of_mem_replicate he⟩
    simp [hkq]
  · obtain ⟨l, hl, hls⟩ := sumPow_nat k q hq hlt
    exact ⟨l, hl, hls, fun h => absurd h hkq⟩

/-- Concatenating the per-gap representations gives one exponent list whose prefix sums hit
every target partition point, and which is identically zero on any gap that keeps its length. -/
lemma exists_exponents : ∀ (n : ℕ) (k q : ℕ → ℕ), (∀ i, i < n → 1 ≤ k i) →
    (∀ i, i < n → 1 ≤ q i) → (∀ i, i < n → q i < 2 ^ (k i)) →
    ∃ L : List ℤ, L.length = ∑ i ∈ Finset.range n, k i ∧
      (∀ m, m ≤ n → ((L.take (∑ i ∈ Finset.range m, k i)).map fun e => (2 : ℝ) ^ e).sum
        = ∑ i ∈ Finset.range m, (q i : ℝ)) ∧
      (∀ i, i < n → k i = q i → ∀ j, ∑ i' ∈ Finset.range i, k i' ≤ j →
        j < ∑ i' ∈ Finset.range (i + 1), k i' → L.getD j 0 = 0) := by
  intro n
  induction n with
  | zero =>
      intro k q _ _ _
      refine ⟨[], by simp, ?_, ?_⟩
      · intro m hm
        have : m = 0 := by omega
        subst this
        simp
      · intro i hi
        omega
  | succ n ih =>
      intro k q hk hq hlt
      obtain ⟨L', hlen', hsum', hz'⟩ := ih k q (fun i hi => hk i (by omega))
        (fun i hi => hq i (by omega)) (fun i hi => hlt i (by omega))
      obtain ⟨l, hl, hls, hlz⟩ := exists_block (k n) (q n) (hq n (by omega)) (hlt n (by omega))
      have hfull : (L' ++ l).length = ∑ i ∈ Finset.range (n + 1), k i := by
        rw [List.length_append, hlen', hl, Finset.sum_range_succ]
      refine ⟨L' ++ l, hfull, ?_, ?_⟩
      · intro m hm
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · have hmn : m ≤ n := by omega
          have hle : ∑ i ∈ Finset.range m, k i ≤ L'.length := by
            rw [hlen']
            have hsub : Finset.range m ⊆ Finset.range n := Finset.range_subset_range.mpr hmn
            exact Finset.sum_le_sum_of_subset hsub
          rw [List.take_append_of_le_length hle]
          exact hsum' m (by omega)
        · have hmn : m = n + 1 := by omega
          subst hmn
          have hLfull : L'.take (∑ i ∈ Finset.range n, k i) = L' := by
            rw [← hlen', List.take_length]
          have hL' : ((L'.map fun e => (2 : ℝ) ^ e).sum) = ∑ i ∈ Finset.range n, (q i : ℝ) := by
            have hh := hsum' n le_rfl
            rwa [hLfull] at hh
          rw [← hfull, List.take_length, List.map_append, List.sum_append, hL', hls,
            Finset.sum_range_succ]
      · intro i hi hkq j hj1 hj2
        rcases Nat.lt_or_ge i n with h | h
        · -- the block lies inside `L'`
          have hjlt : j < L'.length := by
            rw [hlen']
            have hsub : Finset.range (i + 1) ⊆ Finset.range n :=
              Finset.range_subset_range.mpr (by omega)
            have := Finset.sum_le_sum_of_subset (f := k) hsub
            omega
          rw [List.getD_append _ _ _ _ hjlt]
          exact hz' i h hkq j hj1 hj2
        · -- the last block, which is all zeros
          have hin : i = n := by omega
          subst hin
          have hjge : L'.length ≤ j := by rw [hlen']; exact hj1
          rw [List.getD_append_right _ _ _ _ hjge]
          exact getD_eq_zero_of_all (hlz hkq) _

/-! ### The clamp ("ramp") function -/

/-- `ramp a b z` is the length of `[a, b] ∩ (-∞, z]`, for `a ≤ b`. -/
noncomputable def ramp (a b z : ℝ) : ℝ := min (max z a) b - a

lemma ramp_of_le_left {a b z : ℝ} (h : z ≤ a) (hab : a ≤ b) : ramp a b z = 0 := by
  unfold ramp
  rw [max_eq_right h, min_eq_left hab]
  ring

lemma ramp_of_right_le {a b z : ℝ} (h : b ≤ z) (hab : a ≤ b) : ramp a b z = b - a := by
  unfold ramp
  rw [max_eq_left (hab.trans h), min_eq_right h]

lemma ramp_of_mem {a b z : ℝ} (h1 : a ≤ z) (h2 : z ≤ b) : ramp a b z = z - a := by
  unfold ramp
  rw [max_eq_left h1, min_eq_left h2]

lemma ramp_mono (a b : ℝ) : Monotone (ramp a b) := by
  intro z w h
  unfold ramp
  have : max z a ≤ max w a := max_le_max h le_rfl
  exact sub_le_sub_right (min_le_min this le_rfl) a

/-! ### Piecewise-linear data -/

/-- The data of a dyadic piecewise-linear order isomorphism of `[0,1]`: breakpoints `s`,
targets `t`, and slope exponents `e`. -/
structure PLData where
  N : ℕ
  s : ℕ → ℝ
  t : ℕ → ℝ
  e : ℕ → ℤ
  hN : 1 ≤ N
  hs0 : s 0 = 0
  hsN : s N = 1
  ht0 : t 0 = 0
  htN : t N = 1
  hsmono : ∀ j, j < N → s j < s (j + 1)
  hslope : ∀ j, j < N → t (j + 1) - t j = (2 : ℝ) ^ (e j) * (s (j + 1) - s j)
  hsdy : ∀ j, j ≤ N → IsDyadic (s j)
  htdy : ∀ j, j ≤ N → IsDyadic (t j)

namespace PLData

variable (D : PLData)

lemma s_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.N) : D.s i ≤ D.s j := by
  induction j with
  | zero => have : i = 0 := by omega
            simp [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (le_of_lt (D.hsmono j (by omega)))
      · have : i = j + 1 := by omega
        simp [this]

lemma s_nonneg {j : ℕ} (hj : j ≤ D.N) : 0 ≤ D.s j := by
  have := D.s_le (Nat.zero_le j) hj
  rwa [D.hs0] at this

lemma s_le_one {j : ℕ} (hj : j ≤ D.N) : D.s j ≤ 1 := by
  have := D.s_le hj le_rfl
  rwa [D.hsN] at this

lemma t_sub {j : ℕ} (hj : j < D.N) : D.t j < D.t (j + 1) := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (D.e j) := zpow_pos (by norm_num) _
  have h2 : 0 < D.s (j + 1) - D.s j := sub_pos.mpr (D.hsmono j hj)
  have := D.hslope j hj
  nlinarith

lemma t_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.N) : D.t i ≤ D.t j := by
  induction j with
  | zero => have : i = 0 := by omega
            simp [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (le_of_lt (D.t_sub (by omega)))
      · have : i = j + 1 := by omega
        simp [this]

/-- Partial sums of the target gaps: `∑_{j < k} (t (j+1) - t j) = t k`. -/
lemma sum_gaps (k : ℕ) : ∑ j ∈ Finset.range k, (D.t (j + 1) - D.t j) = D.t k - D.t 0 :=
  Finset.sum_range_sub (fun j => D.t j) k

/-- The underlying function. -/
noncomputable def fn (z : ℝ) : ℝ :=
  min z 0 + (∑ j ∈ Finset.range D.N, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z)
    + max (z - 1) 0

lemma fn_monotone : Monotone D.fn := by
  intro z w hzw
  unfold fn
  have h1 : min z 0 ≤ min w 0 := min_le_min hzw le_rfl
  have h2 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        ≤ (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) w := fun j _ =>
    mul_le_mul_of_nonneg_left (ramp_mono _ _ hzw) (le_of_lt (zpow_pos (by norm_num) _))
  have h3 : max (z - 1) 0 ≤ max (w - 1) 0 := max_le_max (sub_le_sub_right hzw 1) le_rfl
  exact add_le_add (add_le_add h1 (Finset.sum_le_sum h2)) h3

lemma fn_of_nonpos {z : ℝ} (hz : z ≤ 0) : D.fn z = z := by
  unfold fn
  have h1 : min z 0 = z := min_eq_left hz
  have h2 : max (z - 1) 0 = 0 := max_eq_right (by linarith)
  have h3 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ramp_of_le_left (hz.trans (D.s_nonneg (by omega)))
      (le_of_lt (D.hsmono j hj)), mul_zero]
  rw [h1, h2, Finset.sum_congr rfl h3]
  simp

lemma total_mass : ∑ j ∈ Finset.range D.N,
    (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) = 1 := by
  have h : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) = D.t (j + 1) - D.t j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (D.hslope j hj).symm
  rw [Finset.sum_congr rfl h, D.sum_gaps D.N, D.ht0, D.htN]
  ring

lemma fn_of_one_le {z : ℝ} (hz : 1 ≤ z) : D.fn z = z := by
  unfold fn
  have h1 : min z 0 = 0 := min_eq_right (by linarith)
  have h2 : max (z - 1) 0 = z - 1 := max_eq_left (by linarith)
  have h3 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        = (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ramp_of_right_le ((D.s_le_one (by omega)).trans hz) (le_of_lt (D.hsmono j hj))]
  rw [h1, h2, Finset.sum_congr rfl h3, D.total_mass]
  ring

/-- The affine formula on the `k`-th piece. -/
lemma fn_piece {k : ℕ} (hk : k < D.N) {z : ℝ} (hz1 : D.s k ≤ z) (hz2 : z ≤ D.s (k + 1)) :
    D.fn z = D.t k + (2 : ℝ) ^ (D.e k) * (z - D.s k) := by
  have hz0 : 0 ≤ z := (D.s_nonneg (by omega)).trans hz1
  have hz1' : z ≤ 1 := hz2.trans (D.s_le_one (by omega))
  unfold fn
  have hmin : min z 0 = 0 := min_eq_right hz0
  have hmax : max (z - 1) 0 = 0 := max_eq_right (by linarith)
  rw [hmin, hmax]
  -- split the sum at `k`
  have hsplit : ∑ j ∈ Finset.range D.N, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
      = (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z)
        + ∑ j ∈ Finset.Ico (k + 1) D.N,
            (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (by omega)]
  have htail : ∑ j ∈ Finset.Ico (k + 1) D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hzs : z ≤ D.s j := hz2.trans (D.s_le (by omega) (by omega))
    rw [ramp_of_le_left hzs (le_of_lt (D.hsmono j (by omega))), mul_zero]
  have hhead : ∑ j ∈ Finset.range k, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
      = D.t k := by
    have h : ∀ j ∈ Finset.range k, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        = D.t (j + 1) - D.t j := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hsj : D.s (j + 1) ≤ z := (D.s_le (by omega) (by omega)).trans hz1
      rw [ramp_of_right_le hsj (le_of_lt (D.hsmono j (by omega)))]
      exact (D.hslope j (by omega)).symm
    rw [Finset.sum_congr rfl h, D.sum_gaps k, D.ht0]
    ring
  rw [hsplit, htail, Finset.sum_range_succ, hhead, ramp_of_mem hz1 hz2]
  ring

/-- The largest breakpoint index at or below a point of `[0,1]`. -/
lemma exists_max_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ k, k ≤ D.N ∧ D.s k ≤ z ∧ ∀ j, j ≤ D.N → D.s j ≤ z → j ≤ k := by
  classical
  have hN := D.hN
  set S : Finset ℕ := (Finset.range (D.N + 1)).filter (fun j => D.s j ≤ z) with hS
  have h0 : 0 ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [D.hs0]; exact hz0⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  refine ⟨S.max' hne, ?_, ?_, ?_⟩
  · have := (Finset.mem_filter.mp (S.max'_mem hne)).1
    rw [Finset.mem_range] at this
    omega
  · exact (Finset.mem_filter.mp (S.max'_mem hne)).2
  · intro j hj hjz
    refine S.le_max' _ ?_
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hjz⟩

/-- Every point of `[0,1]` lies on some piece. -/
lemma exists_piece {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ k, k < D.N ∧ D.s k ≤ z ∧ z ≤ D.s (k + 1) := by
  have hN := D.hN
  obtain ⟨k, hkN, hkz, hmax⟩ := D.exists_max_le hz0 hz1
  rcases Nat.lt_or_ge k D.N with hlt | hge
  · refine ⟨k, hlt, hkz, ?_⟩
    by_contra hc
    push_neg at hc
    have := hmax (k + 1) (by omega) (le_of_lt hc)
    omega
  · -- `k = N`, so `z = 1`; use the last piece
    have hkN' : k = D.N := by omega
    have hz : z = 1 := by
      have h : D.s D.N ≤ z := by rw [← hkN']; exact hkz
      rw [D.hsN] at h
      linarith
    refine ⟨D.N - 1, by omega, ?_, ?_⟩
    · have h : D.s (D.N - 1) ≤ D.s D.N := D.s_le (by omega) le_rfl
      rw [D.hsN] at h
      linarith
    · have h : D.N - 1 + 1 = D.N := by omega
      rw [h, D.hsN, hz]

/-- An interval inside `[0,1]` whose interior avoids every breakpoint lies inside one piece. -/
lemma exists_piece_of_gap {x y : ℝ} (hx0 : 0 ≤ x) (hy1 : y ≤ 1) (hxy : x < y)
    (hgap : ∀ j, j ≤ D.N → D.s j ∉ Set.Ioo x y) :
    ∃ k, k < D.N ∧ D.s k ≤ x ∧ y ≤ D.s (k + 1) := by
  have hN := D.hN
  obtain ⟨k, hkN, hkz, hmax⟩ := D.exists_max_le hx0 (le_of_lt (lt_of_lt_of_le hxy hy1))
  have hklt : k < D.N := by
    rcases Nat.lt_or_ge k D.N with h | h
    · exact h
    · exfalso
      have hkN' : k = D.N := by omega
      have h1 : D.s D.N ≤ x := by rw [← hkN']; exact hkz
      rw [D.hsN] at h1
      linarith
  refine ⟨k, hklt, hkz, ?_⟩
  by_contra hc
  push_neg at hc
  have hgt : x < D.s (k + 1) := by
    by_contra hle
    push_neg at hle
    have := hmax (k + 1) (by omega) hle
    omega
  exact hgap (k + 1) (by omega) ⟨hgt, hc⟩

/-- The map takes each breakpoint to its target. -/
lemma fn_s {j : ℕ} (hj : j ≤ D.N) : D.fn (D.s j) = D.t j := by
  rcases Nat.lt_or_ge j D.N with h | h
  · rw [D.fn_piece h le_rfl (le_of_lt (D.hsmono j h))]; ring
  · have hj' : j = D.N := by omega
    rw [hj', D.hsN, D.fn_of_one_le (le_refl (1 : ℝ)), D.htN]

/-! ### The inverse -/

/-- The inverse data: swap breakpoints and targets, negate the slope exponents. -/
def symm : PLData where
  N := D.N
  s := D.t
  t := D.s
  e := fun j => -(D.e j)
  hN := D.hN
  hs0 := D.ht0
  hsN := D.htN
  ht0 := D.hs0
  htN := D.hsN
  hsmono := fun j hj => D.t_sub hj
  hslope := by
    intro j hj
    have hne : ((2 : ℝ) ^ (D.e j)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
    rw [zpow_neg, D.hslope j hj, inv_mul_cancel_left₀ hne]
  hsdy := D.htdy
  htdy := D.hsdy

@[simp] lemma symm_N : D.symm.N = D.N := rfl
@[simp] lemma symm_s : D.symm.s = D.t := rfl
@[simp] lemma symm_t : D.symm.t = D.s := rfl
@[simp] lemma symm_e (j : ℕ) : D.symm.e j = -(D.e j) := rfl

/-- The image of a piece is the corresponding target piece. -/
lemma fn_mem_piece {k : ℕ} (hk : k < D.N) {z : ℝ} (hz1 : D.s k ≤ z) (hz2 : z ≤ D.s (k + 1)) :
    D.t k ≤ D.fn z ∧ D.fn z ≤ D.t (k + 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (D.e k) := zpow_pos (by norm_num) _
  have hsl := D.hslope k hk
  rw [D.fn_piece hk hz1 hz2]
  constructor
  · nlinarith [sub_nonneg.mpr hz1]
  · nlinarith [sub_nonneg.mpr hz2]

lemma symm_fn_fn (z : ℝ) : D.symm.fn (D.fn z) = z := by
  rcases le_or_gt z 0 with hz | hz
  · rw [D.fn_of_nonpos hz, D.symm.fn_of_nonpos hz]
  rcases le_or_gt 1 z with hz1 | hz1
  · rw [D.fn_of_one_le hz1, D.symm.fn_of_one_le hz1]
  obtain ⟨k, hk, h1, h2⟩ := D.exists_piece (le_of_lt hz) (le_of_lt hz1)
  obtain ⟨ha, hb⟩ := D.fn_mem_piece hk h1 h2
  have hne : ((2 : ℝ) ^ (D.e k)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
  rw [D.symm.fn_piece (show k < D.symm.N from hk) ha hb, D.fn_piece hk h1 h2]
  simp only [symm_t, symm_s, symm_e]
  have hcollapse : D.t k + (2 : ℝ) ^ (D.e k) * (z - D.s k) - D.t k
      = (2 : ℝ) ^ (D.e k) * (z - D.s k) := by ring
  rw [hcollapse, zpow_neg, inv_mul_cancel_left₀ hne]
  ring

lemma symm_symm_fn : D.symm.symm.fn = D.fn := by
  funext z
  simp [fn, symm]

lemma fn_symm_fn (y : ℝ) : D.fn (D.symm.fn y) = y := by
  have h := D.symm.symm_fn_fn y
  rwa [D.symm_symm_fn] at h

lemma fn_injective : Function.Injective D.fn :=
  Function.LeftInverse.injective D.symm_fn_fn

lemma fn_surjective : Function.Surjective D.fn := fun y => ⟨D.symm.fn y, D.fn_symm_fn y⟩

lemma fn_strictMono : StrictMono D.fn :=
  D.fn_monotone.strictMono_of_injective D.fn_injective

/-- The order isomorphism of the line determined by the data. -/
noncomputable def iso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective D.fn D.fn_strictMono D.fn_surjective

@[simp] lemma iso_apply (z : ℝ) : D.iso z = D.fn z := rfl

/-! ### The data defines an element of the line model -/

lemma isThompsonLine_iso : IsThompsonLine D.iso := by
  classical
  refine ⟨fun x hx => D.fn_of_nonpos hx, fun x hx => D.fn_of_one_le hx,
    (Finset.range (D.N + 1)).image D.s, ?_, ?_⟩
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_range] at hj
    exact D.hsdy j (by omega)
  · intro x y hxy hgap
    have hgap' : ∀ j, j ≤ D.N → D.s j ∉ Set.Ioo x y := by
      intro j hj hmem
      have hB : D.s j ∈ (((Finset.range (D.N + 1)).image D.s : Finset ℝ) : Set ℝ) := by
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image]
        exact ⟨j, by simp; omega, rfl⟩
      have hx : D.s j ∈ Set.Ioo x y ∩
          (((Finset.range (D.N + 1)).image D.s : Finset ℝ) : Set ℝ) := ⟨hmem, hB⟩
      rw [hgap] at hx
      exact hx
    rcases le_or_gt y 0 with hy | hy
    · exact ⟨0, 0, fun z hz => by
        rw [iso_apply, D.fn_of_nonpos (hz.2.trans hy)]; simp⟩
    rcases le_or_gt 1 x with hx1 | hx1
    · exact ⟨0, 0, fun z hz => by
        rw [iso_apply, D.fn_of_one_le (hx1.trans hz.1)]; simp⟩
    have hx0 : 0 ≤ x := by
      by_contra hc
      push_neg at hc
      exact hgap' 0 (by omega) (by rw [D.hs0]; exact ⟨hc, hy⟩)
    have hy1 : y ≤ 1 := by
      by_contra hc
      push_neg at hc
      exact hgap' D.N le_rfl (by rw [D.hsN]; exact ⟨hx1, hc⟩)
    obtain ⟨k, hk, h1, h2⟩ := D.exists_piece_of_gap hx0 hy1 hxy hgap'
    refine ⟨D.e k, D.t k - 2 ^ (D.e k) * D.s k, fun z hz => ?_⟩
    rw [iso_apply, D.fn_piece hk (h1.trans hz.1) (hz.2.trans h2)]
    ring

/-! ### Stretches where the data is already the identity -/

lemma t_eq_s_of_zero {a b : ℕ} (hb : b ≤ D.N) (hstart : D.t a = D.s a)
    (hzero : ∀ j, a ≤ j → j < b → D.e j = 0) :
    ∀ j, a ≤ j → j ≤ b → D.t j = D.s j := by
  intro j
  induction j with
  | zero =>
      intro hj1 _
      have : a = 0 := by omega
      rw [← this]; exact hstart
  | succ j ih =>
      intro hj1 hj2
      rcases Nat.lt_or_ge a (j + 1) with h | h
      · have hprev := ih (by omega) (by omega)
        have hsl := D.hslope j (by omega)
        rw [hzero j (by omega) (by omega), zpow_zero, one_mul] at hsl
        linarith
      · have : a = j + 1 := by omega
        rw [← this]; exact hstart

lemma fn_id_on {a b : ℕ} (ha : a ≤ b) (hb : b ≤ D.N)
    (hts : ∀ j, a ≤ j → j ≤ b → D.t j = D.s j)
    (hzero : ∀ j, a ≤ j → j < b → D.e j = 0) :
    ∀ z, D.s a ≤ z → z ≤ D.s b → D.fn z = z := by
  intro z hz1 hz2
  have hz0 : 0 ≤ z := (D.s_nonneg (by omega)).trans hz1
  have hz1' : z ≤ 1 := hz2.trans (D.s_le_one hb)
  obtain ⟨k, hk, h1, h2⟩ := D.exists_piece hz0 hz1'
  rcases Nat.lt_or_ge k a with hka | hka
  · have hle : D.s (k + 1) ≤ D.s a := D.s_le (by omega) (by omega)
    have hzeq : z = D.s a := le_antisymm (h2.trans hle) hz1
    rw [hzeq, D.fn_s (by omega), hts a le_rfl ha]
  · rcases Nat.lt_or_ge k b with hkb | hkb
    · rw [D.fn_piece hk h1 h2, hzero k hka hkb, hts k hka (by omega), zpow_zero]
      ring
    · have hle : D.s b ≤ D.s k := D.s_le hkb (by omega)
      have hzeq : z = D.s b := le_antisymm hz2 (hle.trans h1)
      rw [hzeq, D.fn_s hb, hts b ha le_rfl]

lemma iso_of_le_zero : ∀ x ≤ (0 : ℝ), D.iso x = x := fun x hx => D.fn_of_nonpos hx

lemma iso_of_one_le : ∀ x, (1 : ℝ) ≤ x → D.iso x = x := fun x hx => D.fn_of_one_le hx

end PLData

/-! ### Transfer to the unit-interval model -/

/-- Restricting a line-model element to `[0,1]` gives an interval-model element. -/
lemma isThompson_restrict {L : ℝ ≃o ℝ} (hlo : ∀ x ≤ (0 : ℝ), L x = x)
    (hhi : ∀ x, (1 : ℝ) ≤ x → L x = x)
    (hB : ∃ B : Finset ℝ, (∀ b ∈ B, IsDyadic b) ∧ ∀ x y : ℝ, x < y →
      Set.Ioo x y ∩ (B : Set ℝ) = ∅ →
        ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c) :
    IsThompson (restrict L hlo hhi) := by
  obtain ⟨B, hBdy, hBaff⟩ := hB
  refine ⟨B, hBdy, fun x y hxy hgap => ?_⟩
  obtain ⟨n, c, hc⟩ := hBaff (x : ℝ) (y : ℝ) hxy hgap
  exact ⟨n, c, fun z hz => hc (z : ℝ) hz⟩

/-- The interval-model element determined by piecewise-linear data. -/
noncomputable def PLData.uiMap (D : PLData) : UI ≃o UI :=
  restrict D.iso D.iso_of_le_zero D.iso_of_one_le

lemma PLData.isThompson_uiMap (D : PLData) : IsThompson D.uiMap := by
  refine isThompson_restrict D.iso_of_le_zero D.iso_of_one_le ?_
  obtain ⟨_, _, hB⟩ := D.isThompsonLine_iso
  exact hB

lemma PLData.uiMap_mem_F (D : PLData) : D.uiMap ∈ F :=
  mem_F_of_isThompson D.isThompson_uiMap

@[simp] lemma PLData.uiMap_coe (D : PLData) (z : UI) : ((D.uiMap z : UI) : ℝ) = D.fn (z : ℝ) :=
  rfl


end CFPLib

/-!
## From a tree diagram to its element of `F`

The domain and range trees cut out two standard dyadic partitions of `[0,1]` with the same
number of parts, and corresponding parts have lengths `2 ^ (-p)` and `2 ^ (-q)`, so the ratio is
the integer power of two `2 ^ (p - q)`.  That is exactly the data `PLData` wants, so the element
is built directly, with no refinement — which is what makes it affine on each part rather than
merely piecewise affine.
-/

namespace CannonFloydParry

open CFPLib

/-! ### The marks of a tree form a standard dyadic partition

Reproved here because a solution file may only import the mission's *definitions*. -/

lemma midpoint_halves' {c k : ℕ} :
    ((c : ℝ) / 2 ^ k + ((c : ℝ) + 1) / 2 ^ k) / 2 = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) := by
  have h : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  ring

lemma isChain_marksAux' (t : TTree) :
    ∀ (c k : ℕ), c + 1 ≤ 2 ^ k →
      List.IsChain IsStandardDyadicInterval
        (((c : ℝ) / 2 ^ k) :: (t.marksAux ((c : ℝ) / 2 ^ k) (((c : ℝ) + 1) / 2 ^ k)
          ++ [((c : ℝ) + 1) / 2 ^ k])) := by
  induction t with
  | leaf =>
      intro c k hc
      simp only [TTree.marksAux, List.nil_append]
      exact List.isChain_pair.mpr ⟨c, k, hc, rfl, rfl⟩
  | node l r ihl ihr =>
      intro c k hc
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hc2 : 2 * c + 1 + 1 ≤ 2 ^ (k + 1) := by rw [hpow]; omega
      have hmid : ((c : ℝ) / 2 ^ k + ((c : ℝ) + 1) / 2 ^ k) / 2 = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) :=
        midpoint_halves'
      have hlow : ((2 * c : ℕ) : ℝ) / 2 ^ (k + 1) = (c : ℝ) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      have hhigh : (((2 * c : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) := by
        push_cast; ring
      have htop : (((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((c : ℝ) + 1) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      have hmid' : (((2 * c + 1 : ℕ) : ℝ)) / 2 ^ (k + 1) = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) := by
        push_cast; ring
      have Hl := ihl (2 * c) (k + 1) (by omega)
      have Hr := ihr (2 * c + 1) (k + 1) hc2
      rw [hlow, hhigh] at Hl
      rw [hmid', htop] at Hr
      rw [TTree.marksAux, hmid]
      have := List.IsChain.append_overlap (R := IsStandardDyadicInterval)
        (l₁ := ((c : ℝ) / 2 ^ k) ::
          TTree.marksAux l ((c : ℝ) / 2 ^ k) ((2 * (c : ℝ) + 1) / 2 ^ (k + 1)))
        (l₂ := [(2 * (c : ℝ) + 1) / 2 ^ (k + 1)])
        (l₃ := TTree.marksAux r ((2 * (c : ℝ) + 1) / 2 ^ (k + 1)) (((c : ℝ) + 1) / 2 ^ k)
          ++ [((c : ℝ) + 1) / 2 ^ k])
        (by simpa using Hl) (by simpa using Hr) (by simp)
      simpa using this


/-! ### Elementary facts about standard dyadic intervals and about `marks` -/

lemma sdi_lt' {x y : ℝ} (h : IsStandardDyadicInterval x y) : x < y := by
  obtain ⟨a, n, -, rfl, rfl⟩ := h
  have hp : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have e : ((a : ℝ) + 1) / 2 ^ n - (a : ℝ) / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
  linarith

/-- The ratio of the lengths of two standard dyadic intervals is an integer power of two. -/
lemma slope_of_sdi {x x' y y' : ℝ} (hx : IsStandardDyadicInterval x x')
    (hy : IsStandardDyadicInterval y y') :
    ∃ ee : ℤ, y' - y = 2 ^ ee * (x' - x) := by
  obtain ⟨a, p, -, rfl, rfl⟩ := hx
  obtain ⟨b, q, -, rfl, rfl⟩ := hy
  refine ⟨(p : ℤ) - (q : ℤ), ?_⟩
  have hp0 : ((2 : ℝ) ^ p) ≠ 0 := by positivity
  have hq0 : ((2 : ℝ) ^ q) ≠ 0 := by positivity
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  field_simp
  ring

lemma one_le_leafCount (t : TTree) : 1 ≤ t.leafCount := by
  induction t with
  | leaf => simp [TTree.leafCount]
  | node l r ihl ihr => rw [TTree.leafCount]; omega

lemma marksAux_length : ∀ (t : TTree) (a b : ℝ), (t.marksAux a b).length + 1 = t.leafCount := by
  intro t
  induction t with
  | leaf => intro a b; simp [TTree.marksAux, TTree.leafCount]
  | node l r ihl ihr =>
      intro a b
      rw [TTree.marksAux, TTree.leafCount]
      have h1 := ihl a ((a + b) / 2)
      have h2 := ihr ((a + b) / 2) b
      simp only [List.length_append, List.length_cons]
      omega

lemma marks_length (t : TTree) : t.marks.length = t.leafCount + 1 := by
  show ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).length = t.leafCount + 1
  have := marksAux_length t 0 1
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

lemma isDyadic_half {v : ℝ} (h : IsDyadic v) : IsDyadic (v / 2) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨m, k + 1, ?_⟩
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

lemma isDyadic_one : IsDyadic (1 : ℝ) := ⟨1, 0, by norm_num⟩

lemma marksAux_dyadic : ∀ (t : TTree) (a b : ℝ), IsDyadic a → IsDyadic b →
    ∀ x ∈ t.marksAux a b, IsDyadic x := by
  intro t
  induction t with
  | leaf => intro a b _ _ x hx; simp [TTree.marksAux] at hx
  | node l r ihl ihr =>
      intro a b ha hb x hx
      have hm : IsDyadic ((a + b) / 2) := isDyadic_half (isDyadic_add ha hb)
      rw [TTree.marksAux] at hx
      rcases List.mem_append.mp hx with h | h
      · exact ihl a _ ha hm x h
      · rcases List.mem_cons.mp h with rfl | h
        · exact hm
        · exact ihr _ b hm hb x h

lemma marks_dyadic (t : TTree) : ∀ x ∈ t.marks, IsDyadic x := by
  intro x hx
  have hx' : x ∈ (0 : ℝ) :: (t.marksAux 0 1 ++ [1]) := hx
  rcases List.mem_cons.mp hx' with rfl | h
  · exact isDyadic_zero
  · rcases List.mem_append.mp h with h | h
    · exact marksAux_dyadic t 0 1 isDyadic_zero isDyadic_one x h
    · have : x = 1 := by simpa using h
      subst this; exact isDyadic_one

/-! ### Chains versus indices -/

lemma chain_getD {R : ℝ → ℝ → Prop} : ∀ (xs : List ℝ), List.IsChain R xs →
    ∀ j, j + 1 < xs.length → R (xs.getD j 0) (xs.getD (j + 1) 0) := by
  intro xs
  induction xs with
  | nil => intro _ j hj; simp at hj
  | cons x rest ih =>
      intro hch j hj
      cases j with
      | zero =>
          cases rest with
          | nil => simp at hj
          | cons y t =>
              have := (List.isChain_cons.mp hch).1 y (by simp)
              simpa using this
      | succ j =>
          have hch' := (List.isChain_cons.mp hch).2
          have := ih hch' j (by simpa using hj)
          simpa using this

lemma getD_chain {R : ℝ → ℝ → Prop} : ∀ (xs : List ℝ),
    (∀ j, j + 1 < xs.length → R (xs.getD j 0) (xs.getD (j + 1) 0)) → List.IsChain R xs := by
  intro xs
  induction xs with
  | nil => intro _; exact List.isChain_nil
  | cons x rest ih =>
      intro h
      refine List.isChain_cons.mpr ⟨?_, ih ?_⟩
      · intro y hy
        cases rest with
        | nil => simp at hy
        | cons z t =>
            have hyz : z = y := by simpa using hy
            subst hyz
            have := h 0 (by simp)
            simpa using this
      · intro j hj
        have := h (j + 1) (by simpa using hj)
        simpa using this

lemma getD_getLast : ∀ (xs : List ℝ) (v : ℝ), xs.getLast? = some v →
    xs.getD (xs.length - 1) 0 = v := by
  intro xs
  induction xs with
  | nil => intro v h; simp at h
  | cons x rest ih =>
      intro v h
      cases rest with
      | nil =>
          have : x = v := by simpa using h
          simp [this]
      | cons y t =>
          have h' : (y :: t).getLast? = some v := by
            rw [List.getLast?_cons_cons] at h; exact h
          have hrec := ih v h'
          show (x :: y :: t).getD (t.length + 1) 0 = v
          rw [List.getD_cons_succ]
          simpa using hrec

lemma getD_head {xs : List ℝ} {v : ℝ} (h : xs.head? = some v) : xs.getD 0 0 = v := by
  cases xs with
  | nil => simp at h
  | cons x t =>
      have hxv : x = v := by simpa using h
      simp [hxv]

lemma getD_mem {xs : List ℝ} {j : ℕ} (h : j < xs.length) : xs.getD j 0 ∈ xs := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

/-! ### The extension of a `PLData` map to the line is its underlying function -/

lemma extend_uiMap (D : PLData) (z : ℝ) : extend D.uiMap z = D.fn z := by
  rw [extend_apply]
  by_cases h : z ∈ Set.Icc (0 : ℝ) 1
  · rw [extendFun_of_mem _ h]
    exact D.uiMap_coe ⟨z, h⟩
  · rw [extendFun_of_notMem _ h]
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · exact (D.fn_of_nonpos (le_of_lt h)).symm
    · exact (D.fn_of_one_le (le_of_lt h)).symm

end CannonFloydParry

open CannonFloydParry CFPLib

theorem solution (d : TreeDiagram) : ∃ f : UI ≃o UI, Represents d f := by
  classical
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, ∀ j, X j = d.dom.marks.getD j 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → ℝ, ∀ j, Y j = d.ran.marks.getD j 0 := ⟨_, fun _ => rfl⟩
  set n : ℕ := d.dom.leafCount with hn
  have hPX : IsStandardDyadicPartition d.dom.marks := isStandardDyadicPartition_marks d.dom
  have hPY : IsStandardDyadicPartition d.ran.marks := isStandardDyadicPartition_marks d.ran
  have hlenX : d.dom.marks.length = n + 1 := marks_length d.dom
  have hlenY : d.ran.marks.length = n + 1 := by
    rw [marks_length d.ran, ← d.leaves_eq]
  -- the two partitions, index by index
  have hXsdi : ∀ j, j < n → IsStandardDyadicInterval (X j) (X (j + 1)) := by
    intro j hj
    rw [hXdef, hXdef]
    exact chain_getD _ hPX.2.2 j (by omega)
  have hYsdi : ∀ j, j < n → IsStandardDyadicInterval (Y j) (Y (j + 1)) := by
    intro j hj
    rw [hYdef, hYdef]
    exact chain_getD _ hPY.2.2 j (by omega)
  have hX0 : X 0 = 0 := by
    rw [hXdef]; exact getD_head hPX.1
  have hY0 : Y 0 = 0 := by
    rw [hYdef]; exact getD_head hPY.1
  have hXn : X n = 1 := by
    rw [hXdef]
    have := getD_getLast d.dom.marks 1 hPX.2.1
    rw [hlenX] at this
    simpa using this
  have hYn : Y n = 1 := by
    rw [hYdef]
    have := getD_getLast d.ran.marks 1 hPY.2.1
    rw [hlenY] at this
    simpa using this
  have hXdy : ∀ j, j ≤ n → IsDyadic (X j) := by
    intro j hj
    rw [hXdef]
    exact marks_dyadic d.dom _ (getD_mem (by omega))
  have hYdy : ∀ j, j ≤ n → IsDyadic (Y j) := by
    intro j hj
    rw [hYdef]
    exact marks_dyadic d.ran _ (getD_mem (by omega))
  -- the slope exponents
  have hE : ∀ j : ℕ, ∃ ee : ℤ, j < n → Y (j + 1) - Y j = 2 ^ ee * (X (j + 1) - X j) := by
    intro j
    rcases Nat.lt_or_ge j n with hj | hj
    · obtain ⟨ee, hee⟩ := slope_of_sdi (hXsdi j hj) (hYsdi j hj)
      exact ⟨ee, fun _ => hee⟩
    · exact ⟨0, fun h => absurd h (by omega)⟩
  choose E hEs using hE
  -- the piecewise-linear data
  let D : PLData :=
    { N := n
      s := X
      t := Y
      e := E
      hN := one_le_leafCount d.dom
      hs0 := hX0
      hsN := hXn
      ht0 := hY0
      htN := hYn
      hsmono := fun j hj => sdi_lt' (hXsdi j hj)
      hslope := fun j hj => hEs j hj
      hsdy := hXdy
      htdy := hYdy }
  refine ⟨D.uiMap, D.uiMap_mem_F, ?_, ?_⟩
  · -- affine on each interval of the domain partition
    refine getD_chain _ ?_
    intro j hj
    have hjn : j < n := by rw [hlenX] at hj; omega
    refine ⟨(2 : ℝ) ^ (E j), Y j - (2 : ℝ) ^ (E j) * X j, ?_⟩
    intro z hz
    rw [extend_uiMap]
    rw [← hXdef, ← hXdef] at hz
    have hpc := D.fn_piece (k := j) (by exact hjn) hz.1 hz.2
    rw [hpc]
    ring
  · -- the marks go to the marks
    refine List.ext_getElem (by rw [List.length_map, hlenX, hlenY]) ?_
    intro i h1 h2
    rw [List.getElem_map]
    have hi : i < d.dom.marks.length := by simpa using h1
    have hin : i ≤ n := by rw [hlenX] at hi; omega
    rw [← List.getD_eq_getElem _ _ hi, ← List.getD_eq_getElem _ _ h2, ← hXdef, ← hYdef,
      extend_uiMap]
    exact D.fn_s hin
