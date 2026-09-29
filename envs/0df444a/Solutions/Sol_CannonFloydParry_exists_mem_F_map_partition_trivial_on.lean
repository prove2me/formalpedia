-- Prove2me | solution 1 for CannonFloydParry.exists_mem_F_map_partition_trivial_on
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-15T21:04:35.232516+00:00
-- url     : https://prove2.me/submissions/7627fcea-4440-47e2-805e-8182701f78e2

import Definitions.Def_CannonFloydParry
import Mathlib

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

/-! ### From a pair of integer partitions to the data -/

lemma isDyadic_den {v : ℝ} (h : IsDyadic v) :
    ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, v = (a : ℝ) / 2 ^ M := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨k, fun M hM => ⟨m * 2 ^ (M - k), ?_⟩⟩
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hd : ((2 : ℝ) ^ (M - k)) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ M = 2 ^ k * 2 ^ (M - k) := by
    rw [← pow_add]; congr 1; omega
  rw [h2]
  push_cast
  field_simp

lemma pow_bound (m : ℕ) : 2 * m + 2 < 2 ^ (m + 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have h : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
      omega

lemma sum_take_succ (L : List ℤ) {j : ℕ} (hj : j < L.length) :
    ((L.take (j + 1)).map fun e => (2 : ℝ) ^ e).sum
      = ((L.take j).map fun e => (2 : ℝ) ^ e).sum + (2 : ℝ) ^ (L.getD j 0) := by
  rw [List.take_succ, List.map_append, List.sum_append]
  congr 1
  rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem L 0 hj]
  simp

/-- The core construction.  Two integer partitions of `[0, 2 ^ M₀]` with the same number of
parts give a dyadic piecewise-linear map of `[0,1]` carrying the first to the second, and that
map is the identity on any part the two partitions share. -/
theorem exists_PLData_of_int (n : ℕ) (hn : 1 ≤ n) (M₀ : ℕ) (A B : ℕ → ℤ)
    (hA0 : A 0 = 0) (hAn : A n = 2 ^ M₀) (hB0 : B 0 = 0) (hBn : B n = 2 ^ M₀)
    (hAm : ∀ i, i < n → A i < A (i + 1)) (hBm : ∀ i, i < n → B i < B (i + 1)) :
    ∃ D : PLData,
      (∀ i, i ≤ n → D.fn ((A i : ℝ) / 2 ^ M₀) = (B i : ℝ) / 2 ^ M₀) ∧
      (∀ i, i < n → A i = B i → A (i + 1) = B (i + 1) →
        ∀ z, (A i : ℝ) / 2 ^ M₀ ≤ z → z ≤ (A (i + 1) : ℝ) / 2 ^ M₀ → D.fn z = z) := by
  classical
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = M₀ + 2 := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = M₀ + R := ⟨_, rfl⟩
  have hMR : M < 2 ^ R := by
    have h := pow_bound M₀
    rw [hMdef, hRdef]
    omega
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, ∀ i, K i = (A (i + 1) - A i).toNat * 2 ^ R :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ, ∀ i, Q i = (B (i + 1) - B i).toNat * 2 ^ R :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ i, P i = ∑ i' ∈ Finset.range i, K i' := ⟨_, fun _ => rfl⟩
  obtain ⟨PQ, hPQ⟩ : ∃ PQ : ℕ → ℕ, ∀ i, PQ i = ∑ i' ∈ Finset.range i, Q i' := ⟨_, fun _ => rfl⟩
  -- power bookkeeping
  have hzM : (2 : ℝ) ^ (-(M : ℤ)) = ((2 : ℝ) ^ (M : ℕ))⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hRM : (2 : ℝ) ^ (R : ℕ) * (2 : ℝ) ^ (-(M : ℤ)) = ((2 : ℝ) ^ (M₀ : ℕ))⁻¹ := by
    have h1 : ((2 : ℝ) ^ (M₀ : ℕ)) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) ^ (R : ℕ)) ≠ 0 := by positivity
    rw [hzM, hMdef, pow_add]
    field_simp
  -- each block accounts for one gap
  have hblock : ∀ (C : ℕ → ℤ), (∀ i, i < n → C i < C (i + 1)) → ∀ i, i < n →
      (((C (i + 1) - C i).toNat * 2 ^ R : ℕ) : ℝ) * 2 ^ (-(M : ℤ))
        = (C (i + 1) : ℝ) / 2 ^ M₀ - (C i : ℝ) / 2 ^ M₀ := by
    intro C hC i hi
    have h0 : (0 : ℤ) ≤ C (i + 1) - C i := by have := hC i hi; omega
    have hcast : (((C (i + 1) - C i).toNat : ℕ) : ℝ) = (C (i + 1) : ℝ) - (C i : ℝ) := by
      have h := Int.toNat_of_nonneg h0
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
    have hmain : ((((C (i + 1) - C i).toNat * 2 ^ R : ℕ)) : ℝ)
        = ((C (i + 1) : ℝ) - (C i : ℝ)) * 2 ^ (R : ℕ) := by
      push_cast
      rw [hcast]
    rw [hmain, mul_assoc, hRM]
    ring
  have hblockA : ∀ i, i < n → (K i : ℝ) * 2 ^ (-(M : ℤ))
      = (A (i + 1) : ℝ) / 2 ^ M₀ - (A i : ℝ) / 2 ^ M₀ := by
    intro i hi; rw [hK i]; exact hblock A hAm i hi
  have hblockB : ∀ i, i < n → (Q i : ℝ) * 2 ^ (-(M : ℤ))
      = (B (i + 1) : ℝ) / 2 ^ M₀ - (B i : ℝ) / 2 ^ M₀ := by
    intro i hi; rw [hQ i]; exact hblock B hBm i hi
  -- prefix sums track the partition points
  have hPX : ∀ i, i ≤ n → (P i : ℝ) * 2 ^ (-(M : ℤ)) = (A i : ℝ) / 2 ^ M₀ := by
    intro i
    induction i with
    | zero => intro _; rw [hP 0]; simp [hA0]
    | succ i ih =>
        intro hi
        have hPs : P (i + 1) = P i + K i := by rw [hP, hP, Finset.sum_range_succ]
        rw [hPs, Nat.cast_add, add_mul, ih (by omega), hblockA i (by omega)]
        ring
  have hPY : ∀ i, i ≤ n → (PQ i : ℝ) * 2 ^ (-(M : ℤ)) = (B i : ℝ) / 2 ^ M₀ := by
    intro i
    induction i with
    | zero => intro _; rw [hPQ 0]; simp [hB0]
    | succ i ih =>
        intro hi
        have hPs : PQ (i + 1) = PQ i + Q i := by rw [hPQ, hPQ, Finset.sum_range_succ]
        rw [hPs, Nat.cast_add, add_mul, ih (by omega), hblockB i (by omega)]
        ring
  -- the grid has exactly `2 ^ M` steps
  have hone : (((2 : ℤ) ^ M₀ : ℤ) : ℝ) / 2 ^ (M₀ : ℕ) = 1 := by
    have h2 : ((2 : ℝ) ^ (M₀ : ℕ)) ≠ 0 := by positivity
    push_cast
    field_simp
  have hMne : ((2 : ℝ) ^ (M : ℕ)) ≠ 0 := by positivity
  have hsolve : ∀ c : ℕ, (c : ℝ) * 2 ^ (-(M : ℤ)) = 1 → c = 2 ^ M := by
    intro c hc
    have h := congrArg (fun x : ℝ => x * (2 : ℝ) ^ (M : ℕ)) hc
    simp only [one_mul] at h
    rw [hzM, mul_assoc, inv_mul_cancel₀ hMne, mul_one] at h
    exact_mod_cast h
  have hPn : P n = 2 ^ M := by
    have h := hPX n le_rfl
    rw [hAn, hone] at h
    exact hsolve _ h
  have hPQn : PQ n = 2 ^ M := by
    have h := hPY n le_rfl
    rw [hBn, hone] at h
    exact hsolve _ h
  -- block sizes and the bound that makes the arithmetic lemma apply
  have hKlb : ∀ i, i < n → 2 ^ R ≤ K i := by
    intro i hi
    rw [hK i]
    have h := hAm i hi
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hQlb : ∀ i, i < n → 1 ≤ Q i := by
    intro i hi
    rw [hQ i]
    have h := hBm i hi
    have h1 : 0 < (B (i + 1) - B i).toNat := by omega
    have h2 : 0 < 2 ^ R := by positivity
    have := Nat.mul_pos h1 h2
    omega
  have hQub : ∀ i, i < n → Q i ≤ 2 ^ M := by
    intro i hi
    rw [← hPQn, hPQ n]
    exact Finset.single_le_sum (f := Q) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
  have hQlt : ∀ i, i < n → Q i < 2 ^ (K i) := by
    intro i hi
    have h1 : Q i ≤ 2 ^ M := hQub i hi
    have h2 : (2 : ℕ) ^ M < 2 ^ (2 ^ R) := Nat.pow_lt_pow_right (by norm_num) hMR
    have h3 : (2 : ℕ) ^ (2 ^ R) ≤ 2 ^ (K i) :=
      Nat.pow_le_pow_right (by norm_num) (hKlb i hi)
    omega
  -- the exponent list
  obtain ⟨L, hLlen, hLsum, hLzero⟩ := exists_exponents n K Q
    (fun i hi => le_trans (Nat.one_le_two_pow) (hKlb i hi)) hQlb hQlt
  have hLlen' : L.length = 2 ^ M := by rw [hLlen, ← hP n, hPn]
  -- the prefix sums of the exponent list are the target partition points
  have hTval : ∀ i, i ≤ n →
      ((L.take (P i)).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ)) = (B i : ℝ) / 2 ^ M₀ := by
    intro i hi
    have h := hLsum i hi
    rw [← hP i] at h
    rw [h]
    have h2 : ∑ i' ∈ Finset.range i, (Q i' : ℝ) = ((PQ i : ℕ) : ℝ) := by
      rw [hPQ i]; push_cast; ring
    rw [h2]
    exact hPY i hi
  have hPle : ∀ i, i ≤ n → P i ≤ 2 ^ M := by
    intro i hi
    rw [← hPn, hP i, hP n]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hi)
  -- the data
  obtain ⟨D, hDN, hDs, hDt, hDe⟩ : ∃ D : PLData, D.N = 2 ^ M ∧
      (∀ j, D.s j = (j : ℝ) * 2 ^ (-(M : ℤ))) ∧
      (∀ j, D.t j = ((L.take j).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))) ∧
      (∀ j, D.e j = L.getD j 0) := by
    refine ⟨{ N := 2 ^ M
              s := fun j => (j : ℝ) * 2 ^ (-(M : ℤ))
              t := fun j => ((L.take j).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))
              e := fun j => L.getD j 0
              hN := Nat.one_le_two_pow
              hs0 := by simp
              hsN := ?_
              ht0 := by simp
              htN := ?_
              hsmono := ?_
              hslope := ?_
              hsdy := fun j _ => isDyadic_natDiv j M
              htdy := fun j _ => isDyadic_scaled_sum _ M },
      rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    · show ((2 ^ M : ℕ) : ℝ) * 2 ^ (-(M : ℤ)) = 1
      rw [hzM]
      push_cast
      field_simp
    · show ((L.take (2 ^ M)).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ)) = 1
      have h := hTval n le_rfl
      rw [hPn, hBn, hone] at h
      exact h
    · intro j _
      have hpos : (0 : ℝ) < 2 ^ (-(M : ℤ)) := by positivity
      have hjj : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact mul_lt_mul_of_pos_right hjj hpos
    · intro j hj
      have hjl : j < L.length := by rw [hLlen']; exact hj
      show ((L.take (j + 1)).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))
        - ((L.take j).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))
        = (2 : ℝ) ^ (L.getD j 0) * (((j + 1 : ℕ) : ℝ) * 2 ^ (-(M : ℤ))
          - (j : ℝ) * 2 ^ (-(M : ℤ)))
      rw [sum_take_succ L hjl]
      push_cast
      ring
  refine ⟨D, ?_, ?_⟩
  · -- values at the partition points
    intro i hi
    rw [← hPX i hi, ← hDs (P i), D.fn_s (by rw [hDN]; exact hPle i hi), hDt (P i)]
    exact hTval i hi
  · -- the identity on a shared part
    intro i hi hAB hAB1 z hz1 hz2
    have hKQ : K i = Q i := by rw [hK i, hQ i, hAB, hAB1]
    have hzero : ∀ j, P i ≤ j → j < P (i + 1) → D.e j = 0 := by
      intro j hj1 hj2
      rw [hDe j]
      refine hLzero i hi hKQ j ?_ ?_
      · rwa [← hP i]
      · rwa [← hP (i + 1)]
    have hstart : D.t (P i) = D.s (P i) := by
      rw [hDt (P i), hDs (P i), hTval i (by omega), ← hAB, ← hPX i (by omega)]
    have hle : P i ≤ P (i + 1) := by
      rw [hP i, hP (i + 1)]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    have hbN : P (i + 1) ≤ D.N := by rw [hDN]; exact hPle (i + 1) (by omega)
    have hts := D.t_eq_s_of_zero hbN hstart hzero
    refine D.fn_id_on hle hbN hts hzero z ?_ ?_
    · rw [hDs (P i), hPX i (by omega)]; exact hz1
    · rw [hDs (P (i + 1)), hPX (i + 1) (by omega)]; exact hz2

/-- Cannon–Floyd–Parry's Lemma 4.2, in terms of the underlying function: two dyadic partitions
of `[0,1]` with the same number of parts are carried onto one another, and the map may be taken
to be the identity on a part the two partitions share. -/
theorem exists_PLData_of_partitions (n : ℕ) (hn : 1 ≤ n) (X Y : ℕ → ℝ)
    (hXm : ∀ i, i < n → X i < X (i + 1)) (hYm : ∀ i, i < n → Y i < Y (i + 1))
    (hX0 : X 0 = 0) (hXn : X n = 1) (hY0 : Y 0 = 0) (hYn : Y n = 1)
    (hXd : ∀ i, i ≤ n → IsDyadic (X i)) (hYd : ∀ i, i ≤ n → IsDyadic (Y i)) :
    ∃ D : PLData, (∀ i, i ≤ n → D.fn (X i) = Y i) ∧
      (∀ i, i < n → X i = Y i → X (i + 1) = Y (i + 1) →
        ∀ z, X i ≤ z → z ≤ X (i + 1) → D.fn z = z) := by
  classical
  have hKX : ∀ i, i ≤ n → ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, X i = (a : ℝ) / 2 ^ M :=
    fun i hi => isDyadic_den (hXd i hi)
  have hKY : ∀ i, i ≤ n → ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, Y i = (a : ℝ) / 2 ^ M :=
    fun i hi => isDyadic_den (hYd i hi)
  choose! KX hKXs using hKX
  choose! KY hKYs using hKY
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ i, i ≤ n → KX i ≤ M₀ ∧ KY i ≤ M₀ := by
    refine ⟨(Finset.range (n + 1)).sup (fun i => max (KX i) (KY i)), fun i hi => ⟨?_, ?_⟩⟩
    · refine le_trans (le_max_left (KX i) (KY i)) ?_
      exact Finset.le_sup (f := fun i => max (KX i) (KY i))
        (Finset.mem_range.mpr (by omega : i < n + 1))
    · refine le_trans (le_max_right (KX i) (KY i)) ?_
      exact Finset.le_sup (f := fun i => max (KX i) (KY i))
        (Finset.mem_range.mpr (by omega : i < n + 1))
  have hA : ∀ i, i ≤ n → ∃ a : ℤ, X i = (a : ℝ) / 2 ^ M₀ :=
    fun i hi => hKXs i hi M₀ (hM₀ i hi).1
  have hB : ∀ i, i ≤ n → ∃ b : ℤ, Y i = (b : ℝ) / 2 ^ M₀ :=
    fun i hi => hKYs i hi M₀ (hM₀ i hi).2
  choose! A hAs using hA
  choose! B hBs using hB
  have hpos : (0 : ℝ) < 2 ^ (M₀ : ℕ) := by positivity
  have hne : ((2 : ℝ) ^ (M₀ : ℕ)) ≠ 0 := ne_of_gt hpos
  have hval : ∀ (C : ℕ → ℤ) (Z : ℕ → ℝ), (∀ i, i ≤ n → Z i = (C i : ℝ) / 2 ^ M₀) →
      ∀ i, i ≤ n → (C i : ℝ) = Z i * 2 ^ (M₀ : ℕ) := by
    intro C Z hZ i hi
    rw [hZ i hi]
    field_simp
  have hvA := hval A X hAs
  have hvB := hval B Y hBs
  have hA0 : A 0 = 0 := by
    have h : ((A 0 : ℤ) : ℝ) = 0 := by rw [hvA 0 (by omega), hX0]; ring
    exact_mod_cast h
  have hB0 : B 0 = 0 := by
    have h : ((B 0 : ℤ) : ℝ) = 0 := by rw [hvB 0 (by omega), hY0]; ring
    exact_mod_cast h
  have hAn : A n = 2 ^ M₀ := by
    have h : ((A n : ℤ) : ℝ) = ((2 ^ M₀ : ℤ) : ℝ) := by
      rw [hvA n le_rfl, hXn, one_mul]; push_cast; ring
    exact_mod_cast h
  have hBn : B n = 2 ^ M₀ := by
    have h : ((B n : ℤ) : ℝ) = ((2 ^ M₀ : ℤ) : ℝ) := by
      rw [hvB n le_rfl, hYn, one_mul]; push_cast; ring
    exact_mod_cast h
  have hAm : ∀ i, i < n → A i < A (i + 1) := by
    intro i hi
    have h : ((A i : ℤ) : ℝ) < ((A (i + 1) : ℤ) : ℝ) := by
      rw [hvA i (by omega), hvA (i + 1) (by omega)]
      exact mul_lt_mul_of_pos_right (hXm i hi) hpos
    exact_mod_cast h
  have hBm : ∀ i, i < n → B i < B (i + 1) := by
    intro i hi
    have h : ((B i : ℤ) : ℝ) < ((B (i + 1) : ℤ) : ℝ) := by
      rw [hvB i (by omega), hvB (i + 1) (by omega)]
      exact mul_lt_mul_of_pos_right (hYm i hi) hpos
    exact_mod_cast h
  obtain ⟨D, hD1, hD2⟩ := exists_PLData_of_int n hn M₀ A B hA0 hAn hB0 hBn hAm hBm
  refine ⟨D, ?_, ?_⟩
  · intro i hi
    rw [hAs i hi, hBs i hi]
    exact hD1 i hi
  · intro i hi hXY hXY1 z hz1 hz2
    have hAB : A i = B i := by
      have h : ((A i : ℤ) : ℝ) = ((B i : ℤ) : ℝ) := by
        rw [hvA i (by omega), hvB i (by omega), hXY]
      exact_mod_cast h
    have hAB1 : A (i + 1) = B (i + 1) := by
      have h : ((A (i + 1) : ℤ) : ℝ) = ((B (i + 1) : ℤ) : ℝ) := by
        rw [hvA (i + 1) (by omega), hvB (i + 1) (by omega), hXY1]
      exact_mod_cast h
    refine hD2 i hi hAB hAB1 z ?_ ?_
    · rw [← hAs i (by omega)]; exact hz1
    · rw [← hAs (i + 1) (by omega)]; exact hz2

end CFPLib
open CannonFloydParry CFPLib

theorem solution {n : ℕ} (x y : Fin (n + 1) → UI)
    (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : (x 0 : ℝ) = 0) (hxn : (x (Fin.last n) : ℝ) = 1)
    (hy0 : (y 0 : ℝ) = 0) (hyn : (y (Fin.last n) : ℝ) = 1)
    (hxd : ∀ i, IsDyadic (x i : ℝ)) (hyd : ∀ i, IsDyadic (y i : ℝ))
    (i : Fin n) (hi1 : x i.castSucc = y i.castSucc) (hi2 : x i.succ = y i.succ) :
    ∃ f ∈ F, (∀ j, f (x j) = y j) ∧
      ∀ z : UI, (x i.castSucc : ℝ) ≤ (z : ℝ) → (z : ℝ) ≤ (x i.succ : ℝ) → f z = z := by
  classical
  have hin := i.isLt
  have hn : 1 ≤ n := by omega
  -- reindex the two partitions along `ℕ`
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ, ∀ j, X j =
      ((x ⟨min j n, Nat.lt_succ_of_le (Nat.min_le_right j n)⟩ : UI) : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, ∀ j, Y j =
      ((y ⟨min j n, Nat.lt_succ_of_le (Nat.min_le_right j n)⟩ : UI) : ℝ) := ⟨_, fun _ => rfl⟩
  have hXfin : ∀ i : Fin (n + 1), X (i : ℕ) = ((x i : UI) : ℝ) := by
    intro i
    have hi := i.isLt
    have heq : (⟨min (i : ℕ) n, Nat.lt_succ_of_le (Nat.min_le_right (i : ℕ) n)⟩ :
        Fin (n + 1)) = i := by
      apply Fin.ext
      show min (i : ℕ) n = (i : ℕ)
      omega
    rw [hX, heq]
  have hYfin : ∀ i : Fin (n + 1), Y (i : ℕ) = ((y i : UI) : ℝ) := by
    intro i
    have hi := i.isLt
    have heq : (⟨min (i : ℕ) n, Nat.lt_succ_of_le (Nat.min_le_right (i : ℕ) n)⟩ :
        Fin (n + 1)) = i := by
      apply Fin.ext
      show min (i : ℕ) n = (i : ℕ)
      omega
    rw [hY, heq]
  have hXm : ∀ j, j < n → X j < X (j + 1) := by
    intro j hj
    have e1 : X j = ((x ⟨j, by omega⟩ : UI) : ℝ) := hXfin ⟨j, by omega⟩
    have e2 : X (j + 1) = ((x ⟨j + 1, by omega⟩ : UI) : ℝ) := hXfin ⟨j + 1, by omega⟩
    rw [e1, e2]
    exact hx (by simp [Fin.lt_def])
  have hYm : ∀ j, j < n → Y j < Y (j + 1) := by
    intro j hj
    have e1 : Y j = ((y ⟨j, by omega⟩ : UI) : ℝ) := hYfin ⟨j, by omega⟩
    have e2 : Y (j + 1) = ((y ⟨j + 1, by omega⟩ : UI) : ℝ) := hYfin ⟨j + 1, by omega⟩
    rw [e1, e2]
    exact hy (by simp [Fin.lt_def])
  have hX0' : X 0 = 0 := by
    have h := hXfin 0; rw [Fin.val_zero] at h; rw [h, hx0]
  have hY0' : Y 0 = 0 := by
    have h := hYfin 0; rw [Fin.val_zero] at h; rw [h, hy0]
  have hXn' : X n = 1 := by
    have h := hXfin (Fin.last n); rw [Fin.val_last] at h; rw [h, hxn]
  have hYn' : Y n = 1 := by
    have h := hYfin (Fin.last n); rw [Fin.val_last] at h; rw [h, hyn]
  have hXd' : ∀ j, j ≤ n → IsDyadic (X j) := by
    intro j hj
    have h : X j = ((x ⟨j, by omega⟩ : UI) : ℝ) := hXfin ⟨j, by omega⟩
    rw [h]; exact hxd _
  have hYd' : ∀ j, j ≤ n → IsDyadic (Y j) := by
    intro j hj
    have h : Y j = ((y ⟨j, by omega⟩ : UI) : ℝ) := hYfin ⟨j, by omega⟩
    rw [h]; exact hyd _
  -- the shared part
  have hcs : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := Fin.coe_castSucc i
  have hsu : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
  have hXi : X (i : ℕ) = ((x i.castSucc : UI) : ℝ) := by
    have h := hXfin i.castSucc; rwa [hcs] at h
  have hYi : Y (i : ℕ) = ((y i.castSucc : UI) : ℝ) := by
    have h := hYfin i.castSucc; rwa [hcs] at h
  have hXi1 : X ((i : ℕ) + 1) = ((x i.succ : UI) : ℝ) := by
    have h := hXfin i.succ; rwa [hsu] at h
  have hYi1 : Y ((i : ℕ) + 1) = ((y i.succ : UI) : ℝ) := by
    have h := hYfin i.succ; rwa [hsu] at h
  have hXY : X (i : ℕ) = Y (i : ℕ) := by rw [hXi, hYi, hi1]
  have hXY1 : X ((i : ℕ) + 1) = Y ((i : ℕ) + 1) := by rw [hXi1, hYi1, hi2]
  obtain ⟨D, hD1, hD2⟩ :=
    exists_PLData_of_partitions n hn X Y hXm hYm hX0' hXn' hY0' hYn' hXd' hYd'
  refine ⟨D.uiMap, D.uiMap_mem_F, fun j => ?_, fun z hz1 hz2 => ?_⟩
  · apply Subtype.ext
    rw [PLData.uiMap_coe, ← hXfin j, ← hYfin j]
    exact hD1 (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
  · apply Subtype.ext
    rw [PLData.uiMap_coe]
    refine hD2 (i : ℕ) hin hXY hXY1 (z : ℝ) ?_ ?_
    · rw [hXi]; exact hz1
    · rw [hXi1]; exact hz2
