-- Prove2me | solution 1 for BenfordLaw.factorial_isBenfordSeq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:50:25.229493+00:00
-- url     : https://prove2.me/submissions/96382789-d506-4b64-a93c-350dd5eadbc0

import Mathlib
import Definitions.Def_BenfordLaw_Defs


open Filter Topology

namespace BenfordWeyl

/-- Indicator of `fract t ∈ [a0, a0 + ℓ)`. -/
noncomputable def ind (a0 ℓ t : ℝ) : ℝ :=
  if a0 ≤ Int.fract t ∧ Int.fract t < a0 + ℓ then 1 else 0

lemma ind_nonneg (a0 ℓ t : ℝ) : 0 ≤ ind a0 ℓ t := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (a0 ℓ t : ℝ) : ind a0 ℓ t ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma ind_add_int (a0 ℓ t : ℝ) (m : ℤ) : ind a0 ℓ (t + m) = ind a0 ℓ t := by
  unfold ind; rw [Int.fract_add_intCast]

/-- The indicator as a difference of floors. -/
lemma ind_eq (a0 ℓ z : ℝ) (h0 : 0 ≤ a0) (ha : 0 ≤ ℓ) (h1 : a0 + ℓ ≤ 1) :
    ind a0 ℓ z = (⌊z - a0⌋ : ℝ) - ⌊z - a0 - ℓ⌋ := by
  unfold ind
  have hz : z = Int.fract z + (⌊z⌋ : ℝ) := by rw [Int.fract]; ring
  have e1 : z - a0 = (Int.fract z - a0) + (⌊z⌋ : ℝ) := by linarith
  have e2 : z - a0 - ℓ = (Int.fract z - a0 - ℓ) + (⌊z⌋ : ℝ) := by linarith
  rw [e2, e1, Int.floor_add_intCast, Int.floor_add_intCast]
  have f0 := Int.fract_nonneg z
  have f1 := Int.fract_lt_one z
  by_cases hA : a0 ≤ Int.fract z
  · have k1 : ⌊Int.fract z - a0⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [k1]
    by_cases hB : Int.fract z < a0 + ℓ
    · have k2 : ⌊Int.fract z - a0 - ℓ⌋ = -1 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      rw [if_pos ⟨hA, hB⟩, k2]; norm_num
    · have k2 : ⌊Int.fract z - a0 - ℓ⌋ = 0 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      rw [if_neg (fun h => hB h.2), k2]; norm_num
  · have k1 : ⌊Int.fract z - a0⌋ = -1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    have k2 : ⌊Int.fract z - a0 - ℓ⌋ = -1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [if_neg (fun h => hA h.1), k1, k2]; norm_num

lemma floor_diff_bounds (w b : ℝ) :
    b - 1 ≤ (⌊w⌋ : ℝ) - ⌊w - b⌋ ∧ (⌊w⌋ : ℝ) - ⌊w - b⌋ ≤ b + 1 := by
  have h1 := Int.floor_le w
  have h2 := Int.lt_floor_add_one w
  have h3 := Int.floor_le (w - b)
  have h4 := Int.lt_floor_add_one (w - b)
  constructor <;> linarith

/-- Shifting a progression by one step. -/
lemma step_one (v δ : ℝ) (M : ℕ) :
    M * δ - 1 ≤ ∑ i ∈ Finset.range M, ((⌊v + i * δ⌋ : ℝ) - ⌊v - δ + i * δ⌋) ∧
      ∑ i ∈ Finset.range M, ((⌊v + i * δ⌋ : ℝ) - ⌊v - δ + i * δ⌋) ≤ M * δ + 1 := by
  have ht := Finset.sum_range_sub (fun i : ℕ => (⌊v - δ + i * δ⌋ : ℝ)) M
  have e : ∑ i ∈ Finset.range M, ((⌊v + i * δ⌋ : ℝ) - ⌊v - δ + i * δ⌋) =
      (⌊v - δ + M * δ⌋ : ℝ) - ⌊v - δ + ((0 : ℕ) : ℝ) * δ⌋ := by
    rw [← ht]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    congr 3; ring
  rw [e]
  have := floor_diff_bounds (v - δ + M * δ) (M * δ)
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [show v - δ + M * δ - M * δ = v - δ by ring] at this
  exact this

/-- Shifting a progression by `s` steps. -/
lemma step_s (u δ : ℝ) (M s : ℕ) :
    s * (M * δ - 1) ≤ ∑ i ∈ Finset.range M, ((⌊u + i * δ⌋ : ℝ) - ⌊u - s * δ + i * δ⌋) ∧
      ∑ i ∈ Finset.range M, ((⌊u + i * δ⌋ : ℝ) - ⌊u - s * δ + i * δ⌋) ≤ s * (M * δ + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := step_one (u - s * δ) δ M
    have e : ∑ i ∈ Finset.range M, ((⌊u + i * δ⌋ : ℝ) - ⌊u - ((s + 1 : ℕ) : ℝ) * δ + i * δ⌋) =
        ∑ i ∈ Finset.range M, ((⌊u + i * δ⌋ : ℝ) - ⌊u - s * δ + i * δ⌋) +
        ∑ i ∈ Finset.range M, ((⌊u - s * δ + i * δ⌋ : ℝ) - ⌊u - s * δ - δ + i * δ⌋) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : u - ((s + 1 : ℕ) : ℝ) * δ + i * δ = u - s * δ - δ + i * δ := by push_cast; ring
      rw [this]; ring
    rw [e]
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, h1.1, h1.2]

/-- Counting a progression with step `δ > 0` in a window of length `ℓ`. -/
lemma prog_bound (w δ ℓ : ℝ) (hδ : 0 < δ) (hℓ : 0 ≤ ℓ) (M : ℕ) :
    |∑ i ∈ Finset.range M, ((⌊w + i * δ⌋ : ℝ) - ⌊w - ℓ + i * δ⌋) - M * ℓ| ≤
      M * δ + ℓ / δ + 1 := by
  set r := ⌊ℓ / δ⌋₊ with hr
  have hr1 : (r : ℝ) ≤ ℓ / δ := Nat.floor_le (by positivity)
  have hr2 : ℓ / δ < r + 1 := Nat.lt_floor_add_one _
  have hrδ1 : (r : ℝ) * δ ≤ ℓ := by rwa [le_div_iff₀ hδ] at hr1
  have hrδ2 : ℓ < (r + 1) * δ := by rwa [div_lt_iff₀ hδ] at hr2
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- lower bound
  have lo : ∑ i ∈ Finset.range M, ((⌊w + i * δ⌋ : ℝ) - ⌊w - r * δ + i * δ⌋) ≤
      ∑ i ∈ Finset.range M, ((⌊w + i * δ⌋ : ℝ) - ⌊w - ℓ + i * δ⌋) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have : ⌊w - ℓ + i * δ⌋ ≤ ⌊w - r * δ + i * δ⌋ := Int.floor_mono (by linarith)
    have : (⌊w - ℓ + i * δ⌋ : ℝ) ≤ ⌊w - r * δ + i * δ⌋ := by exact_mod_cast this
    linarith
  have hi : ∑ i ∈ Finset.range M, ((⌊w + i * δ⌋ : ℝ) - ⌊w - ℓ + i * δ⌋) ≤
      ∑ i ∈ Finset.range M, ((⌊w + i * δ⌋ : ℝ) - ⌊w - ((r + 1 : ℕ) : ℝ) * δ + i * δ⌋) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have : ⌊w - ((r + 1 : ℕ) : ℝ) * δ + i * δ⌋ ≤ ⌊w - ℓ + i * δ⌋ :=
      Int.floor_mono (by push_cast; linarith)
    have : (⌊w - ((r + 1 : ℕ) : ℝ) * δ + i * δ⌋ : ℝ) ≤ ⌊w - ℓ + i * δ⌋ := by exact_mod_cast this
    linarith
  have s1 := (step_s w δ M r).1
  have s2 := (step_s w δ M (r + 1)).2
  push_cast at s2 hi
  have m1 : (M : ℝ) * (r * δ) ≤ M * ℓ := mul_le_mul_of_nonneg_left hrδ1 hM
  have m2 : (M : ℝ) * ℓ ≤ M * ((r + 1) * δ) := mul_le_mul_of_nonneg_left hrδ2.le hM
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- There are multiples of an irrational with arbitrarily small positive fractional part. -/
lemma exists_small_fract (θ : ℝ) (hθ : Irrational θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ 0 < Int.fract (k * θ) ∧ Int.fract (k * θ) < ε := by
  have hirr : ∀ K : ℕ, 0 < K → 0 < Int.fract (K * θ) := by
    intro K hK
    have h1 : Irrational (K * θ - ⌊K * θ⌋) := (hθ.natCast_mul hK.ne').sub_intCast _
    have h2 : Int.fract (K * θ) ≠ 0 := h1.ne_zero
    exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h2)
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε')
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  obtain ⟨j, k, hk0, _, hjk⟩ := Real.exists_int_int_abs_mul_sub_le θ hnpos
  have hsmall : |(k : ℝ) * θ - j| < ε' := by
    refine lt_of_le_of_lt hjk ?_
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε'0] at hn
    linarith
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'e : ε' ≤ ε := min_le_left _ _
  have hkn : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    have : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk0.le
    exact_mod_cast this
  have hne : (k : ℝ) * θ - j ≠ 0 := by
    have : Irrational ((k : ℝ) * θ - j) := (hθ.intCast_mul hk0.ne').sub_intCast j
    exact this.ne_zero
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- negative: use a multiple
    set s := j - (k : ℝ) * θ with hs
    have hs0 : 0 < s := by linarith
    have hs1 : s < ε' := by rw [abs_lt] at hsmall; linarith
    set m := ⌊1 / s⌋₊ with hm
    have hm1 : (m : ℝ) ≤ 1 / s := Nat.floor_le (by positivity)
    have hm2 : 1 / s < m + 1 := Nat.lt_floor_add_one _
    have hms1 : (m : ℝ) * s ≤ 1 := by rwa [le_div_iff₀ hs0] at hm1
    have hms2 : 1 < (m + 1) * s := by rwa [div_lt_iff₀ hs0] at hm2
    have hm0 : 0 < m := by
      have : (1 : ℝ) < 1 / s := by rw [lt_div_iff₀ hs0]; linarith
      have : (0 : ℝ) < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hms2; simp at hms2; linarith
        · exact_mod_cast h
      exact_mod_cast this
    refine ⟨m * k.toNat, Nat.mul_pos hm0 (by omega), hirr _ (Nat.mul_pos hm0 (by omega)), ?_⟩
    have hfr : Int.fract (((m * k.toNat : ℕ) : ℝ) * θ) = 1 - m * s := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by nlinarith, m * j - 1, ?_⟩
      push_cast
      rw [hkn, hs]; ring
    rw [hfr]; nlinarith
  · refine ⟨k.toNat, by omega, hirr _ (by omega), ?_⟩
    have hfr : Int.fract ((k.toNat : ℝ) * θ) = (k : ℝ) * θ - j := by
      rw [Int.fract_eq_iff, hkn]
      rw [abs_lt] at hsmall
      exact ⟨hpos.le, by linarith, j, by ring⟩
    rw [hfr]; rw [abs_lt] at hsmall; linarith

/-- Splitting a sum over `range (M * k)` into residue classes mod `k`. -/
lemma sum_range_mul (f : ℕ → ℝ) (M k : ℕ) :
    ∑ n ∈ Finset.range (M * k), f n =
      ∑ i ∈ Finset.range k, ∑ q ∈ Finset.range M, f (q * k + i) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show (M + 1) * k = M * k + k by ring, Finset.sum_range_add, ih,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ]

/-- Floor form of the window indicator; for `0 ≤ ℓ ≤ 1` it is the indicator of
`z mod 1 ∈ [a0, a0 + ℓ) mod 1` (any `a0`). -/
noncomputable def gfl (a0 ℓ z : ℝ) : ℝ := (⌊z - a0⌋ : ℝ) - ⌊z - a0 - ℓ⌋

lemma gfl_add_int (a0 ℓ t : ℝ) (m : ℤ) : gfl a0 ℓ (t + m) = gfl a0 ℓ t := by
  unfold gfl
  rw [show t + m - a0 - ℓ = (t - a0 - ℓ) + m by ring, show t + m - a0 = (t - a0) + m by ring,
    Int.floor_add_intCast, Int.floor_add_intCast]
  push_cast; ring

lemma gfl_nonneg (a0 ℓ t : ℝ) (hℓ : 0 ≤ ℓ) : 0 ≤ gfl a0 ℓ t := by
  unfold gfl
  have : ⌊t - a0 - ℓ⌋ ≤ ⌊t - a0⌋ := Int.floor_mono (by linarith)
  have : (⌊t - a0 - ℓ⌋ : ℝ) ≤ ⌊t - a0⌋ := by exact_mod_cast this
  linarith

lemma gfl_le_one (a0 ℓ t : ℝ) (h1 : ℓ ≤ 1) : gfl a0 ℓ t ≤ 1 := by
  unfold gfl
  have h := Int.floor_mono (show t - a0 - 1 ≤ t - a0 - ℓ by linarith)
  rw [Int.floor_sub_one] at h
  have : (⌊t - a0⌋ : ℝ) - 1 ≤ ⌊t - a0 - ℓ⌋ := by exact_mod_cast h
  linarith

/-- Equidistribution in floor form: works for any window start `a0`. -/
theorem equidistG (θ : ℝ) (hθ : Irrational θ) (x0 a0 ℓ : ℝ) (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, gfl a0 ℓ (x0 + n * θ)) / N) atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk0, hδ0, hδε⟩ := exists_small_fract θ hθ (ε / 2) (by positivity)
  set δ := Int.fract (k * θ) with hδ
  set Cst : ℝ := k * (1 / δ + 3) with hCst
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * Cst / ε)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNbig : 2 * Cst / ε < N := by
    have : (N0 : ℝ) ≤ N := by exact_mod_cast (by omega : N0 ≤ N)
    linarith
  set Count := fun N : ℕ => ∑ n ∈ Finset.range N, gfl a0 ℓ (x0 + n * θ) with hCount
  set M := N / k with hM
  have hMk1 : M * k ≤ N := Nat.div_mul_le_self N k
  have hMk2 : N < M * k + k := by
    exact Nat.lt_div_mul_add hk0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  -- bound on Count (M * k)
  have hblock : |Count (M * k) - (M * k : ℕ) * ℓ| ≤ k * (M * δ + ℓ / δ + 1) := by
    simp only [hCount]
    rw [sum_range_mul]
    have hres : ∀ i ∈ Finset.range k,
        |∑ q ∈ Finset.range M, gfl a0 ℓ (x0 + ((q * k + i : ℕ) : ℝ) * θ) - M * ℓ| ≤
          M * δ + ℓ / δ + 1 := by
      intro i _
      have e : ∀ q : ℕ, gfl a0 ℓ (x0 + ((q * k + i : ℕ) : ℝ) * θ) =
          (⌊(x0 + i * θ - a0) + q * δ⌋ : ℝ) - ⌊(x0 + i * θ - a0) - ℓ + q * δ⌋ := by
        intro q
        have : x0 + ((q * k + i : ℕ) : ℝ) * θ =
            (x0 + i * θ + q * δ) + ((q * ⌊(k : ℝ) * θ⌋ : ℤ) : ℝ) := by
          rw [hδ, Int.fract]; push_cast; ring
        rw [this, gfl_add_int]; unfold gfl
        congr 3 <;> ring
      simp only [e]
      exact prog_bound _ δ ℓ hδ0 hℓ M
    have := Finset.abs_sum_le_sum_abs
      (fun i => ∑ q ∈ Finset.range M, gfl a0 ℓ (x0 + ((q * k + i : ℕ) : ℝ) * θ) - M * ℓ)
      (Finset.range k)
    rw [Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have h2 := Finset.sum_le_sum hres
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have hc : ((M * k : ℕ) : ℝ) * ℓ = k * (M * ℓ) := by push_cast; ring
    rw [hc]
    exact this.trans h2
  -- tail
  have htail : 0 ≤ Count N - Count (M * k) ∧ Count N - Count (M * k) ≤ k := by
    have e : Count N = Count (M * k) +
        ∑ n ∈ Finset.range (N - M * k), gfl a0 ℓ (x0 + ((M * k + n : ℕ) : ℝ) * θ) := by
      simp only [hCount]
      rw [← Finset.sum_range_add, Nat.add_sub_cancel' hMk1]
    rw [e, add_sub_cancel_left]
    constructor
    · exact Finset.sum_nonneg fun n _ => gfl_nonneg _ _ _ hℓ
    · calc _ ≤ ∑ n ∈ Finset.range (N - M * k), (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => gfl_le_one _ _ _ h1
        _ = ((N - M * k : ℕ) : ℝ) := by simp
        _ ≤ k := by exact_mod_cast (by omega : N - M * k ≤ k)
  have hMkR : ((M * k : ℕ) : ℝ) ≤ N := by exact_mod_cast hMk1
  have hMkR2 : (N : ℝ) - k ≤ ((M * k : ℕ) : ℝ) := by
    have : N ≤ M * k + k := hMk2.le
    have : (N : ℝ) ≤ ((M * k : ℕ) : ℝ) + k := by exact_mod_cast this
    linarith
  have hMδ : (M : ℝ) * k * δ ≤ N * δ := by
    have : ((M * k : ℕ) : ℝ) = (M : ℝ) * k := by push_cast; ring
    nlinarith
  have hℓ1 : ℓ ≤ 1 := h1
  have hℓδ : ℓ / δ ≤ 1 / δ := div_le_div_of_nonneg_right hℓ1 hδ0.le
  -- total error
  have herr : |Count N - N * ℓ| ≤ N * δ + Cst := by
    have e : Count N - N * ℓ = (Count N - Count (M * k)) +
        (Count (M * k) - (M * k : ℕ) * ℓ) - (N - (M * k : ℕ)) * ℓ := by ring
    rw [e]
    have hb := abs_le.mp hblock
    have hpart : 0 ≤ (N - ((M * k : ℕ) : ℝ)) * ℓ ∧ (N - ((M * k : ℕ) : ℝ)) * ℓ ≤ k := by
      constructor
      · exact mul_nonneg (by linarith) hℓ
      · nlinarith
    rw [hCst, abs_le]
    constructor <;> nlinarith [htail.1, htail.2, hb.1, hb.2, hpart.1, hpart.2]
  rw [Real.dist_eq]
  show |Count N / N - ℓ| < ε
  rw [show Count N / N - ℓ = (Count N - N * ℓ) / N by field_simp, abs_div,
    abs_of_pos hNpos, div_lt_iff₀ hNpos]
  have : 2 * Cst < ε * N := by rw [div_lt_iff₀ hε] at hNbig; linarith
  have : (N : ℝ) * δ < N * (ε / 2) := mul_lt_mul_of_pos_left hδε hNpos
  linarith

/-- **Equidistribution of `x0 + nθ` modulo 1** for irrational `θ`, tested on intervals. -/
theorem equidist (θ : ℝ) (hθ : Irrational θ) (x0 a0 ℓ : ℝ) (h0 : 0 ≤ a0) (hℓ : 0 ≤ ℓ)
    (h1 : a0 + ℓ ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ind a0 ℓ (x0 + n * θ)) / N) atTop (𝓝 ℓ) := by
  refine (equidistG θ hθ x0 a0 ℓ hℓ (by linarith)).congr fun N => ?_
  congr 1
  exact Finset.sum_congr rfl fun n _ => (ind_eq a0 ℓ _ h0 hℓ h1).symm

end BenfordWeyl


open Filter Topology BenfordWeyl

namespace BenfordFac

lemma tele (F : ℕ → ℝ) (M s : ℕ) :
    ∑ q ∈ Finset.range M, (F (q + s) - F q) = ∑ q ∈ Finset.range s, (F (q + M) - F q) := by
  have h1 := Finset.sum_range_add F s M
  have h2 := Finset.sum_range_add F M s
  rw [add_comm s M] at h1
  have e1 : ∑ q ∈ Finset.range M, F (q + s) = ∑ q ∈ Finset.range M, F (s + q) :=
    Finset.sum_congr rfl fun q _ => by rw [add_comm]
  have e2 : ∑ q ∈ Finset.range s, F (q + M) = ∑ q ∈ Finset.range s, F (M + q) :=
    Finset.sum_congr rfl fun q _ => by rw [add_comm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, e1, e2]
  linarith

lemma gfl_shift_sum (a0 ℓ : ℝ) (w : ℕ → ℝ) (M s : ℕ) (h1 : ℓ ≤ 1) (hℓ : 0 ≤ ℓ) :
    ∑ q ∈ Finset.range M, gfl a0 ℓ (w (q + s)) ≤ ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) + s ∧
    ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) ≤ ∑ q ∈ Finset.range M, gfl a0 ℓ (w (q + s)) + s := by
  have h := Finset.sum_range_add (fun q => gfl a0 ℓ (w q)) M s
  have h' := Finset.sum_range_add (fun q => gfl a0 ℓ (w q)) s M
  rw [add_comm s M] at h'
  have b1 : ∑ q ∈ Finset.range s, gfl a0 ℓ (w (M + q)) ≤ s := by
    calc _ ≤ ∑ q ∈ Finset.range s, (1 : ℝ) := Finset.sum_le_sum fun q _ => gfl_le_one _ _ _ h1
      _ = s := by simp
  have b2 : ∑ q ∈ Finset.range s, gfl a0 ℓ (w q) ≤ s := by
    calc _ ≤ ∑ q ∈ Finset.range s, (1 : ℝ) := Finset.sum_le_sum fun q _ => gfl_le_one _ _ _ h1
      _ = s := by simp
  have c1 : 0 ≤ ∑ q ∈ Finset.range s, gfl a0 ℓ (w (M + q)) :=
    Finset.sum_nonneg fun q _ => gfl_nonneg _ _ _ hℓ
  have c2 : 0 ≤ ∑ q ∈ Finset.range s, gfl a0 ℓ (w q) :=
    Finset.sum_nonneg fun q _ => gfl_nonneg _ _ _ hℓ
  simp only [add_comm s] at h'
  constructor <;> linarith

lemma floor_sub_bounds (u v : ℝ) :
    u - v - 1 ≤ (⌊u⌋ : ℝ) - ⌊v⌋ ∧ (⌊u⌋ : ℝ) - ⌊v⌋ ≤ u - v + 1 := by
  have := Int.floor_le u; have := Int.lt_floor_add_one u
  have := Int.floor_le v; have := Int.lt_floor_add_one v
  constructor <;> linarith

/-- Final algebra common to both directions. -/
lemma final_alg (C M ℓ d1 d2 : ℝ) (s1 s2 : ℕ) (hd1 : 0 < d1) (hd : d1 ≤ d2) (hℓ : 0 ≤ ℓ)
    (h1 : ℓ ≤ 1) (hM : 0 ≤ M) (hC0 : 0 ≤ C)
    (hs1 : (s1 : ℝ) ≤ ℓ / d1 + 1) (hs2 : ℓ / d2 - 1 ≤ s2)
    (hup : C ≤ s1 * (M * d2 + 2)) (hlo : s2 * (M * d1 - 2) ≤ C) :
    |C - M * ℓ| ≤ M * ℓ * (d2 - d1) / d1 + M * d2 + 2 * ℓ / d1 + 2 := by
  have hd2 : 0 < d2 := lt_of_lt_of_le hd1 hd
  have k1 : ℓ / d2 ≤ ℓ / d1 := div_le_div_of_nonneg_left hℓ hd1 hd
  have kd : ℓ * d1 / d2 ≥ ℓ - ℓ * (d2 - d1) / d1 := by
    rw [ge_iff_le, sub_le_iff_le_add]
    have : ℓ * (d2 - d1) / d2 ≤ ℓ * (d2 - d1) / d1 :=
      div_le_div_of_nonneg_left (by nlinarith) hd1 hd
    have e : ℓ = ℓ * d1 / d2 + ℓ * (d2 - d1) / d2 := by field_simp; ring
    linarith
  have hT0 : 0 ≤ M * ℓ * (d2 - d1) / d1 := div_nonneg (by nlinarith [mul_nonneg hM hℓ]) hd1.le
  have hT1 : 0 ≤ 2 * ℓ / d1 := by positivity
  have hT2 : 0 ≤ M * d2 := by positivity
  rw [abs_le]; constructor
  · by_cases hA : M * d1 < 2
    · have : M * ℓ ≤ 2 * ℓ / d1 := by
        rw [le_div_iff₀ hd1]; nlinarith
      linarith
    by_cases hB : ℓ < d2
    · have : M * ℓ ≤ M * d2 := by nlinarith
      linarith
    push Not at hA hB
    have hs2' : 0 ≤ ℓ / d2 - 1 := by rw [sub_nonneg, le_div_iff₀ hd2]; linarith
    have : (ℓ / d2 - 1) * (M * d1 - 2) ≤ s2 * (M * d1 - 2) :=
      mul_le_mul_of_nonneg_right hs2 (by linarith)
    have ex : (ℓ / d2 - 1) * (M * d1 - 2) = M * (ℓ * d1 / d2) - 2 * (ℓ / d2) - M * d1 + 2 := by
      field_simp; ring
    have : M * (ℓ * d1 / d2) ≥ M * (ℓ - ℓ * (d2 - d1) / d1) := mul_le_mul_of_nonneg_left kd hM
    have e3 : M * (ℓ - ℓ * (d2 - d1) / d1) = M * ℓ - M * ℓ * (d2 - d1) / d1 := by ring
    have : M * d1 ≤ M * d2 := mul_le_mul_of_nonneg_left hd hM
    have e4 : 2 * (ℓ / d1) = 2 * ℓ / d1 := by ring
    linarith
  · have : (s1 : ℝ) * (M * d2 + 2) ≤ (ℓ / d1 + 1) * (M * d2 + 2) :=
      mul_le_mul_of_nonneg_right hs1 (by positivity)
    have ex : (ℓ / d1 + 1) * (M * d2 + 2) =
        M * ℓ + M * ℓ * (d2 - d1) / d1 + 2 * ℓ / d1 + M * d2 + 2 := by field_simp; ring
    linarith

lemma sum_card_bounds (a0 ℓ : ℝ) (w : ℕ → ℝ) (M : ℕ) (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) :
    0 ≤ ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) ∧ ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) ≤ M := by
  constructor
  · exact Finset.sum_nonneg fun q _ => gfl_nonneg _ _ _ hℓ
  · calc _ ≤ ∑ q ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum fun q _ => gfl_le_one _ _ _ h1
      _ = M := by simp

/-- Counting an increasing slowly-varying progression in a window. -/
theorem vprog_inc (a0 ℓ d1 d2 : ℝ) (w : ℕ → ℝ) (M : ℕ) (hd1 : 0 < d1) (hd : d1 ≤ d2)
    (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) (hw : ∀ q, d1 ≤ w (q + 1) - w q ∧ w (q + 1) - w q ≤ d2) :
    |∑ q ∈ Finset.range M, gfl a0 ℓ (w q) - M * ℓ| ≤
      M * ℓ * (d2 - d1) / d1 + M * d2 + 2 * ℓ / d1 + 2 := by
  have hd2 : 0 < d2 := lt_of_lt_of_le hd1 hd
  have hmul : ∀ q s : ℕ, s * d1 ≤ w (q + s) - w q ∧ w (q + s) - w q ≤ s * d2 := by
    intro q s
    induction s with
    | zero => simp
    | succ s ih =>
      have := hw (q + s)
      rw [← add_assoc]; push_cast
      constructor <;> linarith [ih.1, ih.2]
  set s1 := ⌈ℓ / d1⌉₊ with hs1
  set s2 := ⌊ℓ / d2⌋₊ with hs2
  have hs1a : ℓ / d1 ≤ s1 := Nat.le_ceil _
  have hs1b : (s1 : ℝ) ≤ ℓ / d1 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hs2a : (s2 : ℝ) ≤ ℓ / d2 := Nat.floor_le (by positivity)
  have hs2b : ℓ / d2 - 1 ≤ s2 := by linarith [Nat.lt_floor_add_one (ℓ / d2)]
  have hs1c : ℓ ≤ s1 * d1 := by rwa [div_le_iff₀ hd1] at hs1a
  have hs2c : s2 * d2 ≤ ℓ := by rwa [le_div_iff₀ hd2] at hs2a
  set F : ℕ → ℝ := fun q => (⌊w q - a0⌋ : ℝ) with hF
  have hFM : ∀ q, (M : ℝ) * d1 - 1 ≤ F (q + M) - F q ∧ F (q + M) - F q ≤ M * d2 + 1 := by
    intro q
    have := floor_sub_bounds (w (q + M) - a0) (w q - a0)
    have := hmul q M
    simp only [hF]; constructor <;> linarith
  -- upper
  have hup1 : ∀ q, gfl a0 ℓ (w (q + s1)) ≤ F (q + s1) - F q := by
    intro q; unfold gfl; simp only [hF]
    have := (hmul q s1).1
    have : ⌊w q - a0⌋ ≤ ⌊w (q + s1) - a0 - ℓ⌋ := Int.floor_mono (by linarith)
    have : (⌊w q - a0⌋ : ℝ) ≤ ⌊w (q + s1) - a0 - ℓ⌋ := by exact_mod_cast this
    linarith
  have hup : ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) ≤ s1 * (M * d2 + 2) := by
    have a := (gfl_shift_sum a0 ℓ w M s1 h1 hℓ).2
    have b : ∑ q ∈ Finset.range M, gfl a0 ℓ (w (q + s1)) ≤
        ∑ q ∈ Finset.range M, (F (q + s1) - F q) := Finset.sum_le_sum fun q _ => hup1 q
    rw [tele] at b
    have c : ∑ q ∈ Finset.range s1, (F (q + M) - F q) ≤ ∑ q ∈ Finset.range s1, ((M : ℝ) * d2 + 1) :=
      Finset.sum_le_sum fun q _ => (hFM q).2
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at c
    nlinarith
  -- lower
  have hlo1 : ∀ q, F (q + s2) - F q ≤ gfl a0 ℓ (w (q + s2)) := by
    intro q; unfold gfl; simp only [hF]
    have := (hmul q s2).2
    have : ⌊w (q + s2) - a0 - ℓ⌋ ≤ ⌊w q - a0⌋ := Int.floor_mono (by linarith)
    have : (⌊w (q + s2) - a0 - ℓ⌋ : ℝ) ≤ ⌊w q - a0⌋ := by exact_mod_cast this
    linarith
  have hlo : s2 * (M * d1 - 2) ≤ ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) := by
    have a := (gfl_shift_sum a0 ℓ w M s2 h1 hℓ).1
    have b : ∑ q ∈ Finset.range M, (F (q + s2) - F q) ≤
        ∑ q ∈ Finset.range M, gfl a0 ℓ (w (q + s2)) := Finset.sum_le_sum fun q _ => hlo1 q
    rw [tele] at b
    have c : ∑ q ∈ Finset.range s2, ((M : ℝ) * d1 - 1) ≤ ∑ q ∈ Finset.range s2, (F (q + M) - F q) :=
      Finset.sum_le_sum fun q _ => (hFM q).1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at c
    nlinarith
  have hb := sum_card_bounds a0 ℓ w M hℓ h1
  exact final_alg _ M ℓ d1 d2 s1 s2 hd1 hd hℓ h1 (Nat.cast_nonneg M) hb.1 hs1b hs2b hup hlo

/-- Counting a decreasing slowly-varying progression in a window. -/
theorem vprog_dec (a0 ℓ d1 d2 : ℝ) (w : ℕ → ℝ) (M : ℕ) (hd1 : 0 < d1) (hd : d1 ≤ d2)
    (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) (hw : ∀ q, d1 ≤ w q - w (q + 1) ∧ w q - w (q + 1) ≤ d2) :
    |∑ q ∈ Finset.range M, gfl a0 ℓ (w q) - M * ℓ| ≤
      M * ℓ * (d2 - d1) / d1 + M * d2 + 2 * ℓ / d1 + 2 := by
  have hd2 : 0 < d2 := lt_of_lt_of_le hd1 hd
  have hmul : ∀ q s : ℕ, s * d1 ≤ w q - w (q + s) ∧ w q - w (q + s) ≤ s * d2 := by
    intro q s
    induction s with
    | zero => simp
    | succ s ih =>
      have := hw (q + s)
      rw [← add_assoc]; push_cast
      constructor <;> linarith [ih.1, ih.2]
  set s1 := ⌈ℓ / d1⌉₊ with hs1
  set s2 := ⌊ℓ / d2⌋₊ with hs2
  have hs1a : ℓ / d1 ≤ s1 := Nat.le_ceil _
  have hs1b : (s1 : ℝ) ≤ ℓ / d1 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hs2a : (s2 : ℝ) ≤ ℓ / d2 := Nat.floor_le (by positivity)
  have hs2b : ℓ / d2 - 1 ≤ s2 := by linarith [Nat.lt_floor_add_one (ℓ / d2)]
  have hs1c : ℓ ≤ s1 * d1 := by rwa [div_le_iff₀ hd1] at hs1a
  have hs2c : s2 * d2 ≤ ℓ := by rwa [le_div_iff₀ hd2] at hs2a
  set F : ℕ → ℝ := fun q => (⌊w q - a0⌋ : ℝ) with hF
  have hFM : ∀ q, (M : ℝ) * d1 - 1 ≤ F q - F (q + M) ∧ F q - F (q + M) ≤ M * d2 + 1 := by
    intro q
    have := floor_sub_bounds (w q - a0) (w (q + M) - a0)
    have := hmul q M
    simp only [hF]; constructor <;> linarith
  have hup1 : ∀ q, gfl a0 ℓ (w q) ≤ F q - F (q + s1) := by
    intro q; unfold gfl; simp only [hF]
    have := (hmul q s1).1
    have : ⌊w (q + s1) - a0⌋ ≤ ⌊w q - a0 - ℓ⌋ := Int.floor_mono (by linarith)
    have : (⌊w (q + s1) - a0⌋ : ℝ) ≤ ⌊w q - a0 - ℓ⌋ := by exact_mod_cast this
    linarith
  have hup : ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) ≤ s1 * (M * d2 + 2) := by
    have b : ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) ≤
        ∑ q ∈ Finset.range M, (F q - F (q + s1)) := Finset.sum_le_sum fun q _ => hup1 q
    have t := tele F M s1
    have e1 : ∑ q ∈ Finset.range M, (F q - F (q + s1)) = -∑ q ∈ Finset.range M, (F (q + s1) - F q) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext q; ring
    have e2 : ∑ q ∈ Finset.range s1, (F (q + M) - F q) = -∑ q ∈ Finset.range s1, (F q - F (q + M)) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext q; ring
    have c : ∑ q ∈ Finset.range s1, (F q - F (q + M)) ≤ ∑ q ∈ Finset.range s1, ((M : ℝ) * d2 + 1) :=
      Finset.sum_le_sum fun q _ => (hFM q).2
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at c
    nlinarith
  have hlo1 : ∀ q, F q - F (q + s2) ≤ gfl a0 ℓ (w q) := by
    intro q; unfold gfl; simp only [hF]
    have := (hmul q s2).2
    have : ⌊w q - a0 - ℓ⌋ ≤ ⌊w (q + s2) - a0⌋ := Int.floor_mono (by linarith)
    have : (⌊w q - a0 - ℓ⌋ : ℝ) ≤ ⌊w (q + s2) - a0⌋ := by exact_mod_cast this
    linarith
  have hlo : s2 * (M * d1 - 2) ≤ ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) := by
    have b : ∑ q ∈ Finset.range M, (F q - F (q + s2)) ≤
        ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) := Finset.sum_le_sum fun q _ => hlo1 q
    have t := tele F M s2
    have e1 : ∑ q ∈ Finset.range M, (F q - F (q + s2)) = -∑ q ∈ Finset.range M, (F (q + s2) - F q) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext q; ring
    have e2 : ∑ q ∈ Finset.range s2, (F (q + M) - F q) = -∑ q ∈ Finset.range s2, (F q - F (q + M)) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext q; ring
    have c : ∑ q ∈ Finset.range s2, ((M : ℝ) * d1 - 1) ≤ ∑ q ∈ Finset.range s2, (F q - F (q + M)) :=
      Finset.sum_le_sum fun q _ => (hFM q).1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at c
    have : (s2 : ℝ) * (M * d1 - 2) ≤ s2 * (M * d1 - 1) := by nlinarith [(Nat.cast_nonneg s2 : (0:ℝ) ≤ s2)]
    linarith
  have hb := sum_card_bounds a0 ℓ w M hℓ h1
  exact final_alg _ M ℓ d1 d2 s1 s2 hd1 hd hℓ h1 (Nat.cast_nonneg M) hb.1 hs1b hs2b hup hlo

/-- Version with hypotheses only on the relevant range. -/
theorem vprog_inc' (a0 ℓ d1 d2 : ℝ) (w : ℕ → ℝ) (M : ℕ) (hd1 : 0 < d1) (hd : d1 ≤ d2)
    (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1)
    (hw : ∀ q, q + 1 < M → d1 ≤ w (q + 1) - w q ∧ w (q + 1) - w q ≤ d2) :
    |∑ q ∈ Finset.range M, gfl a0 ℓ (w q) - M * ℓ| ≤
      M * ℓ * (d2 - d1) / d1 + M * d2 + 2 * ℓ / d1 + 2 := by
  set v : ℕ → ℝ := fun q => if q + 1 < M then w q else w (M - 1) + ((q : ℝ) + 1 - M) * d1 with hv
  have hsum : ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) = ∑ q ∈ Finset.range M, gfl a0 ℓ (v q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_range] at hq
    simp only [hv]
    split_ifs with h
    · rfl
    · have : q = M - 1 := by omega
      subst this
      congr 2
      have : ((M - 1 : ℕ) : ℝ) + 1 = M := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; ring
  rw [hsum]
  refine vprog_inc a0 ℓ d1 d2 v M hd1 hd hℓ h1 fun q => ?_
  simp only [hv]
  by_cases h2 : q + 1 + 1 < M
  · rw [if_pos h2, if_pos (by omega)]; exact hw q (by omega)
  · rw [if_neg h2]
    by_cases h3 : q + 1 < M
    · rw [if_pos h3]
      have hM1 : M - 1 = q + 1 := by omega
      rw [hM1]
      have h0 : ((q + 1 : ℕ) : ℝ) + 1 - M = 0 := by
        have : q + 1 + 1 = M := by omega
        rw [← this]; push_cast; ring
      rw [h0, zero_mul, add_zero]
      exact hw q h3
    · rw [if_neg h3]
      push_cast
      constructor <;> nlinarith

theorem vprog_dec' (a0 ℓ d1 d2 : ℝ) (w : ℕ → ℝ) (M : ℕ) (hd1 : 0 < d1) (hd : d1 ≤ d2)
    (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1)
    (hw : ∀ q, q + 1 < M → d1 ≤ w q - w (q + 1) ∧ w q - w (q + 1) ≤ d2) :
    |∑ q ∈ Finset.range M, gfl a0 ℓ (w q) - M * ℓ| ≤
      M * ℓ * (d2 - d1) / d1 + M * d2 + 2 * ℓ / d1 + 2 := by
  set v : ℕ → ℝ := fun q => if q + 1 < M then w q else w (M - 1) - ((q : ℝ) + 1 - M) * d1 with hv
  have hsum : ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) = ∑ q ∈ Finset.range M, gfl a0 ℓ (v q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_range] at hq
    simp only [hv]
    split_ifs with h
    · rfl
    · have : q = M - 1 := by omega
      subst this
      congr 2
      have : ((M - 1 : ℕ) : ℝ) + 1 = M := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; ring
  rw [hsum]
  refine vprog_dec a0 ℓ d1 d2 v M hd1 hd hℓ h1 fun q => ?_
  simp only [hv]
  by_cases h2 : q + 1 + 1 < M
  · rw [if_pos h2, if_pos (by omega)]; exact hw q (by omega)
  · rw [if_neg h2]
    by_cases h3 : q + 1 < M
    · rw [if_pos h3]
      have hM1 : M - 1 = q + 1 := by omega
      rw [hM1]
      have h0 : ((q + 1 : ℕ) : ℝ) + 1 - M = 0 := by
        have : q + 1 + 1 = M := by omega
        rw [← this]; push_cast; ring
      rw [h0, zero_mul, sub_zero]
      exact hw q h3
    · rw [if_neg h3]
      push_cast
      constructor <;> nlinarith

end BenfordFac


open Filter Topology BenfordWeyl

namespace BenfordFac

noncomputable def xf (n : ℕ) : ℝ := Real.logb 10 ((n + 1).factorial : ℝ)

lemma xf_add (n k : ℕ) :
    xf (n + k) - xf n = ∑ t ∈ Finset.range k, Real.logb 10 ((n + 2 + t : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : xf (n + (k + 1)) = Real.logb 10 ((n + 2 + k : ℕ) : ℝ) + xf (n + k) := by
      unfold xf
      rw [show n + (k + 1) + 1 = (n + k + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity)]
      congr 2; ring
    rw [e]; ring

lemma one_lt_log_ten : 1 < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

lemma logb_diff_bound (a N R : ℝ) (hN : 0 < N) (ha : N ≤ a) (hR : a ≤ N + R) :
    0 ≤ Real.logb 10 a - Real.logb 10 N ∧ Real.logb 10 a - Real.logb 10 N ≤ R / N := by
  have ha0 : 0 < a := lt_of_lt_of_le hN ha
  rw [← Real.logb_div ha0.ne' hN.ne']
  have h1 : 1 ≤ a / N := by rw [le_div_iff₀ hN]; linarith
  have hl0 : 0 ≤ Real.log (a / N) := Real.log_nonneg h1
  constructor
  · exact Real.logb_nonneg (by norm_num) h1
  · rw [Real.logb]
    have h10 := one_lt_log_ten
    have : Real.log (a / N) / Real.log 10 ≤ Real.log (a / N) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : Real.log (a / N) ≤ a / N - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : a / N - 1 ≤ R / N := by
      rw [div_sub_one hN.ne', div_le_div_iff_of_pos_right hN]; linarith
    linarith

lemma step_bound (N n k R : ℕ) (hN : 1 ≤ N) (hn : N ≤ n) (hR : n + k + 1 ≤ N + R) :
    0 ≤ xf (n + k) - xf n - k * Real.logb 10 N ∧
      xf (n + k) - xf n - k * Real.logb 10 N ≤ k * R / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [xf_add]
  have e : ∑ t ∈ Finset.range k, Real.logb 10 ((n + 2 + t : ℕ) : ℝ) - k * Real.logb 10 N =
      ∑ t ∈ Finset.range k, (Real.logb 10 ((n + 2 + t : ℕ) : ℝ) - Real.logb 10 N) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  have hb : ∀ t ∈ Finset.range k, 0 ≤ Real.logb 10 ((n + 2 + t : ℕ) : ℝ) - Real.logb 10 N ∧
      Real.logb 10 ((n + 2 + t : ℕ) : ℝ) - Real.logb 10 N ≤ R / N := by
    intro t ht
    rw [Finset.mem_range] at ht
    refine logb_diff_bound _ _ _ hN0 ?_ ?_
    · exact_mod_cast (by omega : N ≤ n + 2 + t)
    · exact_mod_cast (by omega : n + 2 + t ≤ N + R)
  constructor
  · exact Finset.sum_nonneg fun t ht => (hb t ht).1
  · calc _ ≤ ∑ t ∈ Finset.range k, ((R : ℝ) / N) := Finset.sum_le_sum fun t ht => (hb t ht).2
      _ = k * R / N := by simp; ring

/-- One residue class of a block. -/
theorem class_bound (a0 ℓ η ε τ : ℝ) (N k M i : ℕ) (j : ℤ) (hN : 1 ≤ N) (hk : 1 ≤ k) (hi : i < k)
    (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) (hη : 0 < η) (hτ : (k : ℝ) * (k * M) / N ≤ τ) (h2τ : 2 * τ ≤ η)
    (hδ1 : η ≤ |k * Real.logb 10 N - j|) (hδ2 : |k * Real.logb 10 N - j| ≤ ε) :
    |∑ q ∈ Finset.range M, gfl a0 ℓ (xf (N + (q * k + i))) - M * ℓ| ≤
      2 * M * τ / η + M * (ε + τ) + 4 / η + 2 := by
  set δ := k * Real.logb 10 N - j with hδ
  set w : ℕ → ℝ := fun q => xf (N + (q * k + i)) - q * j with hw
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ
  have hsum : ∑ q ∈ Finset.range M, gfl a0 ℓ (xf (N + (q * k + i))) =
      ∑ q ∈ Finset.range M, gfl a0 ℓ (w q) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hw]
    rw [show xf (N + (q * k + i)) - q * j = xf (N + (q * k + i)) + ((-(q * j) : ℤ) : ℝ) by
      push_cast; ring, gfl_add_int]
  rw [hsum]
  have hstep : ∀ q, q + 1 < M → δ ≤ w (q + 1) - w q ∧ w (q + 1) - w q ≤ δ + τ := by
    intro q hq
    have hsb := step_bound N (N + (q * k + i)) k (k * M) hN (by omega) (by nlinarith)
    have e : w (q + 1) - w q = (xf (N + (q * k + i) + k) - xf (N + (q * k + i)) -
        k * Real.logb 10 N) + δ := by
      simp only [hw, hδ]
      rw [show N + ((q + 1) * k + i) = N + (q * k + i) + k by ring]
      push_cast; ring
    rw [e]
    have : (k : ℝ) * ((k * M : ℕ) : ℝ) / N ≤ τ := by push_cast; exact hτ
    constructor <;> linarith [hsb.1, hsb.2]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases le_or_gt 0 δ with hpos | hneg
  · rw [abs_of_nonneg hpos] at hδ1 hδ2
    have hd1 : 0 < δ := lt_of_lt_of_le hη hδ1
    have hb := vprog_inc' a0 ℓ δ (δ + τ) w M hd1 (by linarith) hℓ h1 hstep
    have k1 : M * ℓ * (δ + τ - δ) / δ ≤ 2 * M * τ / η := by
      rw [show δ + τ - δ = τ by ring, div_le_div_iff₀ hd1 hη]
      have : M * ℓ * τ ≤ M * τ := by nlinarith [mul_nonneg hM hτ0]
      nlinarith [mul_nonneg hM hτ0]
    have k2 : 2 * ℓ / δ ≤ 4 / η := by
      rw [div_le_div_iff₀ hd1 hη]; nlinarith
    have k3 : M * (δ + τ) ≤ M * (ε + τ) := by nlinarith
    linarith
  · rw [abs_of_neg hneg] at hδ1 hδ2
    have hd1 : 0 < -δ - τ := by linarith
    have hstep' : ∀ q, q + 1 < M → -δ - τ ≤ w q - w (q + 1) ∧ w q - w (q + 1) ≤ -δ := by
      intro q hq; have := hstep q hq; constructor <;> linarith
    have hb := vprog_dec' a0 ℓ (-δ - τ) (-δ) w M hd1 (by linarith) hℓ h1 hstep'
    have hd1' : η / 2 ≤ -δ - τ := by linarith
    have k1 : M * ℓ * (-δ - (-δ - τ)) / (-δ - τ) ≤ 2 * M * τ / η := by
      rw [show -δ - (-δ - τ) = τ by ring, div_le_div_iff₀ hd1 hη]
      have : M * ℓ * τ ≤ M * τ := by nlinarith [mul_nonneg hM hτ0]
      nlinarith [mul_nonneg hM hτ0]
    have k2 : 2 * ℓ / (-δ - τ) ≤ 4 / η := by
      rw [div_le_div_iff₀ hd1 hη]; nlinarith
    have k3 : M * (-δ) ≤ M * (ε + τ) := by nlinarith
    linarith

/-- A whole block of length `M * k` starting at `N`. -/
theorem block_bound (a0 ℓ η ε τ : ℝ) (N k M : ℕ) (j : ℤ) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) (hη : 0 < η) (hτ : (k : ℝ) * (k * M) / N ≤ τ) (h2τ : 2 * τ ≤ η)
    (hδ1 : η ≤ |k * Real.logb 10 N - j|) (hδ2 : |k * Real.logb 10 N - j| ≤ ε) :
    |∑ n ∈ Finset.range (M * k), gfl a0 ℓ (xf (N + n)) - (M * k : ℕ) * ℓ| ≤
      (M * k : ℕ) * (2 * τ / η + ε + τ) + k * (4 / η + 2) := by
  rw [sum_range_mul (fun n => gfl a0 ℓ (xf (N + n)))]
  have hres := fun i (hi : i ∈ Finset.range k) =>
    class_bound a0 ℓ η ε τ N k M i j hN hk (Finset.mem_range.mp hi) hℓ h1 hη hτ h2τ hδ1 hδ2
  have := Finset.abs_sum_le_sum_abs
    (fun i => ∑ q ∈ Finset.range M, gfl a0 ℓ (xf (N + (q * k + i))) - M * ℓ) (Finset.range k)
  rw [Finset.sum_sub_distrib] at this
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have h2 := Finset.sum_le_sum hres
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hc : ((M * k : ℕ) : ℝ) * ℓ = k * (M * ℓ) := by push_cast; ring
  rw [hc]
  refine (this.trans h2).trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

end BenfordFac


open Filter Topology BenfordWeyl

namespace BenfordFac

lemma gfl_near_int (η z : ℝ) (j : ℤ) (hη : 0 < η) (hη1 : 2 * η ≤ 1) (h : |z - j| < η) :
    gfl (-η) (2 * η) z = 1 := by
  rw [abs_lt] at h
  unfold gfl
  have e1 : ⌊z - -η⌋ = j := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  have e2 : ⌊z - -η - 2 * η⌋ = j - 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [e1, e2]; push_cast; ring

lemma log_ten_lt_three : Real.log 10 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h2 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  norm_num at h2; linarith

lemma log_one_add_inv_bounds (m : ℝ) (hm : 0 < m) :
    1 / (m + 1) ≤ Real.log ((m + 1) / m) ∧ Real.log ((m + 1) / m) ≤ 1 / m := by
  constructor
  · have := Real.one_sub_inv_le_log_of_pos (show 0 < (m + 1) / m by positivity)
    rw [inv_div] at this
    have e : 1 - m / (m + 1) = 1 / (m + 1) := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos (show 0 < (m + 1) / m by positivity)
    have e : (m + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith

/-- Few block starts have `k log₁₀ (bB)` close to an integer. -/
theorem bad_count (η : ℝ) (B k b0 Y : ℕ) (hη : 0 < η) (hη1 : 2 * η ≤ 1) (hB : 1 ≤ B)
    (hk : 1 ≤ k) (hb0 : 1 ≤ b0) (hY : b0 ≤ Y) :
    ∑ q ∈ Finset.range (Y - b0), gfl (-η) (2 * η) (k * Real.logb 10 (((b0 + q) * B : ℕ) : ℝ)) ≤
      2 * η * Y * (Y / b0) + k * Y / b0 + 14 * η * Y + 2 := by
  set M := Y - b0 with hM
  have hl := one_lt_log_ten
  have hl3 := log_ten_lt_three
  have hb0R : (1 : ℝ) ≤ b0 := by exact_mod_cast hb0
  have hYR : (b0 : ℝ) ≤ Y := by exact_mod_cast hY
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : (0 : ℝ) < Y := by linarith
  set d1 : ℝ := k / (Y * Real.log 10) with hd1
  set d2 : ℝ := k / (b0 * Real.log 10) with hd2
  have hd10 : 0 < d1 := by positivity
  have hd12 : d1 ≤ d2 := by
    rw [hd1, hd2]; apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hstep : ∀ q, q + 1 < M →
      d1 ≤ k * Real.logb 10 (((b0 + (q + 1)) * B : ℕ) : ℝ) -
        k * Real.logb 10 (((b0 + q) * B : ℕ) : ℝ) ∧
      k * Real.logb 10 (((b0 + (q + 1)) * B : ℕ) : ℝ) -
        k * Real.logb 10 (((b0 + q) * B : ℕ) : ℝ) ≤ d2 := by
    intro q hq
    set m : ℝ := ((b0 + q : ℕ) : ℝ) with hm
    have hm0 : 0 < m := by rw [hm]; exact_mod_cast (by omega : 0 < b0 + q)
    have hBR : (0 : ℝ) < B := by exact_mod_cast hB
    have e : k * Real.logb 10 (((b0 + (q + 1)) * B : ℕ) : ℝ) -
        k * Real.logb 10 (((b0 + q) * B : ℕ) : ℝ) = k * (Real.log ((m + 1) / m) / Real.log 10) := by
      rw [← mul_sub, ← Real.logb_div (by positivity) (by positivity), Real.logb]
      congr 3
      rw [hm]; push_cast; field_simp; ring
    rw [e]
    have hb := log_one_add_inv_bounds m hm0
    have hmY : m + 1 ≤ Y := by rw [hm]; exact_mod_cast (by omega : b0 + q + 1 ≤ Y)
    have hmb : (b0 : ℝ) ≤ m := by rw [hm]; exact_mod_cast (by omega : b0 ≤ b0 + q)
    constructor
    · rw [hd1, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 1 / Y ≤ Real.log ((m + 1) / m) :=
        le_trans (one_div_le_one_div_of_le (by positivity) hmY) hb.1
      rw [div_le_iff₀ hY0] at this
      have h' := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ k * Real.log 10)
      linarith
    · rw [hd2, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : Real.log ((m + 1) / m) ≤ 1 / b0 :=
        le_trans hb.2 (one_div_le_one_div_of_le (by positivity) hmb)
      rw [le_div_iff₀ (by positivity)] at this
      have h' := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ k * Real.log 10)
      linarith
  have hb := vprog_inc' (-η) (2 * η) d1 d2
    (fun q => k * Real.logb 10 (((b0 + q) * B : ℕ) : ℝ)) M hd10 hd12 (by linarith) hη1 hstep
  have hMR : (M : ℝ) ≤ Y := by rw [hM]; exact_mod_cast (by omega : Y - b0 ≤ Y)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hr : d2 / d1 = Y / b0 := by rw [hd1, hd2]; field_simp
  have t1 : M * (2 * η) * (d2 - d1) / d1 ≤ 2 * η * Y * (Y / b0) := by
    have : M * (2 * η) * (d2 - d1) / d1 ≤ M * (2 * η) * (d2 / d1) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) hd10.le
    rw [hr] at this
    have : M * (2 * η) * (Y / b0) ≤ Y * (2 * η) * (Y / b0) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    nlinarith
  have t2 : M * d2 ≤ k * Y / b0 := by
    rw [hd2]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : (M : ℝ) * k * b0 ≤ Y * k * b0 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
    have h6 : (Y : ℝ) * k * b0 * 1 ≤ Y * k * b0 * Real.log 10 :=
      mul_le_mul_of_nonneg_left hl.le (by positivity)
    linarith
  have t3 : 2 * (2 * η) / d1 ≤ 12 * η * Y := by
    rw [hd1, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hη hY0]
  have t4 : M * (2 * η) ≤ 2 * η * Y := by nlinarith
  have := (abs_le.mp hb).2
  linarith

end BenfordFac


open Filter Topology BenfordWeyl

namespace BenfordFac

theorem block_case (a0 ℓ η ε τ : ℝ) (K m b b0 : ℕ) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hb0 : 1 ≤ b0) (hb : b0 ≤ b) (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) (hη : 0 < η) (hη1 : 2 * η ≤ 1)
    (hε : 1 / ((K : ℝ) + 1) ≤ ε) (hτ : (K : ℝ) / b0 ≤ τ) (h2τ : 2 * τ ≤ η) :
    |∑ n ∈ Finset.range (K.factorial * m), gfl a0 ℓ (xf (b * (K.factorial * m) + n)) -
        ((K.factorial * m : ℕ) : ℝ) * ℓ| ≤
      ((K.factorial * m : ℕ) : ℝ) * (2 * τ / η + ε + τ) + K * (4 / η + 2) +
      ((K.factorial * m : ℕ) : ℝ) * ∑ k' ∈ Finset.range K,
        gfl (-η) (2 * η) (((k' + 1 : ℕ) : ℝ) * Real.logb 10 ((b * (K.factorial * m) : ℕ) : ℝ)) := by
  set L := K.factorial with hL
  set B := L * m with hB
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K)
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set θ := Real.logb 10 ((b * B : ℕ) : ℝ) with hθ
  set S := ∑ k' ∈ Finset.range K, gfl (-η) (2 * η) (((k' + 1 : ℕ) : ℝ) * θ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k' _ => gfl_nonneg _ _ _ (by linarith)
  have hBR : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hrest : 0 ≤ (B : ℝ) * S := mul_nonneg hBR hS0
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ
  have hG0 : 0 ≤ (B : ℝ) * (2 * τ / η + ε + τ) + K * (4 / η + 2) := by
    have : 0 ≤ ε := le_trans (by positivity) hε
    positivity
  obtain ⟨j, kz, hkz0, hkzK, hdir⟩ := Real.exists_int_int_abs_mul_sub_le θ (n := K) (by omega)
  set k := kz.toNat with hk
  have hkz : ((k : ℕ) : ℤ) = kz := Int.toNat_of_nonneg hkz0.le
  have hkR : ((k : ℕ) : ℝ) = (kz : ℝ) := by exact_mod_cast hkz
  have hk1 : 1 ≤ k := by omega
  have hkK : k ≤ K := by omega
  rw [← hkR] at hdir
  have hKR : ((K : ℕ) : ℝ) + 1 = (K : ℝ) + 1 := rfl
  rcases lt_or_ge |(k : ℝ) * θ - j| η with hbad | hgood
  · -- bad case
    have hg : gfl (-η) (2 * η) (((k - 1 + 1 : ℕ) : ℝ) * θ) = 1 := by
      rw [show k - 1 + 1 = k by omega]; exact gfl_near_int η _ j hη hη1 hbad
    have hS1 : 1 ≤ S := by
      rw [← hg, hS]
      exact Finset.single_le_sum (f := fun k' => gfl (-η) (2 * η) (((k' + 1 : ℕ) : ℝ) * θ))
        (fun k' _ => gfl_nonneg _ _ _ (by linarith)) (Finset.mem_range.mpr (by omega))
    have hcb := sum_card_bounds a0 ℓ (fun n => xf (b * B + n)) B hℓ h1
    have : |∑ n ∈ Finset.range B, gfl a0 ℓ (xf (b * B + n)) - (B : ℝ) * ℓ| ≤ B := by
      rw [abs_le]; constructor <;> nlinarith
    have : (B : ℝ) ≤ B * S := by nlinarith
    linarith
  · -- good case
    have hkL : k ∣ L := Nat.dvd_factorial (by omega) hkK
    set M := L / k * m with hM
    have hMk : M * k = B := by
      rw [hM, hB, mul_comm (L / k) m, mul_assoc, Nat.div_mul_cancel hkL, mul_comm]
    have hN : 1 ≤ b * B := Nat.mul_pos (by omega) hB1
    have hτ' : (k : ℝ) * (k * M) / ((b * B : ℕ) : ℝ) ≤ τ := by
      have e : (k : ℝ) * M = B := by exact_mod_cast (by rw [mul_comm]; exact hMk : k * M = B)
      rw [e]
      have hb0R : (1 : ℝ) ≤ b0 := by exact_mod_cast hb0
      have hbR : (b0 : ℝ) ≤ b := by exact_mod_cast hb
      have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
      have : (k : ℝ) * B / ((b * B : ℕ) : ℝ) = k / b := by
        push_cast; field_simp
      rw [this]
      have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
      calc (k : ℝ) / b ≤ K / b := div_le_div_of_nonneg_right hkKR (by linarith)
        _ ≤ K / b0 := div_le_div_of_nonneg_left (by positivity) (by linarith) hbR
        _ ≤ τ := hτ
    have hdir' : |(k : ℝ) * θ - j| ≤ ε := le_trans hdir hε
    have hbb := block_bound a0 ℓ η ε τ (b * B) k M j hN hk1 hℓ h1 hη hτ' h2τ hgood hdir'
    rw [hMk] at hbb
    have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have : (k : ℝ) * (4 / η + 2) ≤ K * (4 / η + 2) :=
      mul_le_mul_of_nonneg_right hkKR (by positivity)
    linarith

end BenfordFac


open Filter Topology BenfordWeyl

namespace BenfordFac

lemma block_decomp (f : ℕ → ℝ) (Y B : ℕ) :
    ∑ n ∈ Finset.range (Y * B), f n = ∑ b ∈ Finset.range Y, ∑ n ∈ Finset.range B, f (b * B + n) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [show (Y + 1) * B = Y * B + B by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]

set_option maxHeartbeats 1000000 in
theorem main_bound (a0 ℓ ε : ℝ) (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4)
    (K : ℕ) (hK : 1 ≤ K) (hKε : 1 / ((K : ℝ) + 1) ≤ ε) (X m : ℕ) (hm1 : 1 ≤ m) (hmX : m * m ≤ X)
    (ha : 3 * (K.factorial : ℝ) ≤ m)
    (hb : 3 * K / (ε * (ε ^ 2 / K)) ≤ ε * (m / K.factorial - 1))
    (hc : (K.factorial : ℝ) * (2 + K * (K / ε + 2)) ≤ ε * m)
    (hd : (K : ℝ) * (4 / (ε ^ 2 / K) + 2) ≤ ε * K.factorial * m) :
    |∑ n ∈ Finset.range X, gfl a0 ℓ (xf n) - X * ℓ| ≤ 11 * ε * X := by
  set L := K.factorial with hL
  set η : ℝ := ε ^ 2 / K with hη
  set B := L * m with hB
  set Y := X / B with hY
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hB1 : 1 ≤ B := Nat.mul_pos hL1 hm1
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ ε ^ 2 := div_le_self (by positivity) hKR
  have hε2 : ε ^ 2 ≤ ε / 4 := by
    have := mul_le_mul_of_nonneg_left hε hε0.le; rw [pow_two]; linarith
  have hηh : 2 * η ≤ 1 := by linarith
  have hηle : η ≤ 1 := by linarith
  have hYB : Y * B ≤ X := Nat.div_mul_le_self X B
  have hYB2 : X < Y * B + B := Nat.lt_div_mul_add hB1
  have hYBR : (Y : ℝ) * B ≤ X := by exact_mod_cast hYB
  have hYBR2 : (X : ℝ) < Y * B + B := by exact_mod_cast hYB2
  have hXm : (m : ℝ) * m ≤ X := by exact_mod_cast hmX
  -- Y is large
  have hYm : (m : ℝ) / L - 1 < Y := by
    have : (m : ℝ) * m < (Y + 1) * (L * m) := by
      have : (B : ℝ) = L * m := by rw [hB]; push_cast; ring
      have : (X : ℝ) < (Y + 1) * B := by linarith
      calc (m : ℝ) * m ≤ X := hXm
        _ < (Y + 1) * B := this
        _ = (Y + 1) * (L * m) := by rw [‹(B : ℝ) = L * m›]
    rw [div_sub_one (by positivity), div_lt_iff₀ (by positivity)]
    have e : ((Y : ℝ) + 1) * (L * m) = (Y * L + L) * m := by ring
    rw [e] at this
    have := lt_of_mul_lt_mul_right this (by positivity)
    linarith
  have hY2 : (2 : ℝ) ≤ Y := by
    have : (3 : ℝ) ≤ m / L := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  set b0 := ⌊ε * Y⌋₊ + 1 with hb0
  have hb0a : ε * Y < b0 := by rw [hb0]; push_cast; exact Nat.lt_floor_add_one _
  have hb0b : (b0 : ℝ) ≤ ε * Y + 1 := by
    rw [hb0]; push_cast; linarith [Nat.floor_le (show 0 ≤ ε * Y by positivity)]
  have hb01 : 1 ≤ b0 := by omega
  have hb0R : (1 : ℝ) ≤ b0 := by exact_mod_cast hb01
  have hb0Y : b0 ≤ Y := by
    have : ε * Y ≤ 1 / 4 * Y := mul_le_mul_of_nonneg_right hε (by positivity)
    have : (b0 : ℝ) ≤ Y := by linarith
    exact_mod_cast this
  set τ : ℝ := K / b0 with hτ
  -- τ is small
  have hb0big : 3 * K / (ε * η) ≤ b0 := by
    have : ε * ((m : ℝ) / L - 1) ≤ ε * Y := mul_le_mul_of_nonneg_left hYm.le hε0.le
    linarith
  have hτs : τ ≤ ε * η / 3 := by
    have hpos : 0 < 3 * K / (ε * η) := by positivity
    calc τ = K / b0 := hτ
      _ ≤ K / (3 * K / (ε * η)) := div_le_div_of_nonneg_left (by positivity) hpos hb0big
      _ = ε * η / 3 := by field_simp
  have hτ0 : 0 ≤ τ := by positivity
  have hεη : ε * η ≤ η / 4 := by
    have := mul_le_mul_of_nonneg_right hε hη0.le; linarith
  have h2τ : 2 * τ ≤ η := by linarith
  have hτη : 2 * τ / η + τ ≤ ε := by
    have : 2 * τ / η ≤ 2 * ε / 3 := by
      rw [div_le_iff₀ hη0]; linarith
    have : ε * η ≤ ε := by
      have := mul_le_mul_of_nonneg_left hηle hε0.le; linarith
    linarith
  -- decomposition
  set f : ℕ → ℝ := fun n => gfl a0 ℓ (xf n) with hf
  set Blk : ℕ → ℝ := fun b => ∑ n ∈ Finset.range B, f (b * B + n) with hBlk
  set S : ℕ → ℝ := fun b => ∑ k' ∈ Finset.range K,
    gfl (-η) (2 * η) (((k' + 1 : ℕ) : ℝ) * Real.logb 10 ((b * B : ℕ) : ℝ)) with hS
  set G : ℝ := (B : ℝ) * (2 * τ / η + ε + τ) + K * (4 / η + 2) with hG
  have hKε' : 1 / ((K : ℝ) + 1) ≤ ε := hKε
  have hcase : ∀ q, |Blk (b0 + q) - B * ℓ| ≤ G + B * S (b0 + q) := by
    intro q
    have := block_case a0 ℓ η ε τ K m (b0 + q) b0 hK hm1 hb01 (by omega) hℓ h1 hη0 hηh hKε'
      le_rfl h2τ
    simpa [hBlk, hS, hG, hf, hB, hL] using this
  have hcard : ∀ b, |Blk b - B * ℓ| ≤ B := by
    intro b
    have hcb := sum_card_bounds a0 ℓ (fun n => xf (b * B + n)) B hℓ h1
    rw [abs_le]; constructor <;> nlinarith
  have hsplit : ∑ n ∈ Finset.range X, f n - X * ℓ =
      ∑ b ∈ Finset.range b0, (Blk b - B * ℓ) + ∑ q ∈ Finset.range (Y - b0), (Blk (b0 + q) - B * ℓ) +
      (∑ n ∈ Finset.range (X - Y * B), f (Y * B + n) - ((X : ℝ) - Y * B) * ℓ) := by
    have e1 : ∑ n ∈ Finset.range X, f n =
        ∑ n ∈ Finset.range (Y * B), f n + ∑ n ∈ Finset.range (X - Y * B), f (Y * B + n) := by
      rw [← Finset.sum_range_add, Nat.add_sub_cancel' hYB]
    have e2 : ∑ n ∈ Finset.range (Y * B), f n =
        ∑ b ∈ Finset.range b0, Blk b + ∑ q ∈ Finset.range (Y - b0), Blk (b0 + q) := by
      rw [block_decomp, ← Finset.sum_range_add, Nat.add_sub_cancel' hb0Y]
    rw [e1, e2, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((Y - b0 : ℕ) : ℝ) = Y - b0 := by rw [Nat.cast_sub hb0Y]
    rw [this]; ring
  -- piece 1
  have p1 : |∑ b ∈ Finset.range b0, (Blk b - B * ℓ)| ≤ b0 * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ b ∈ Finset.range b0, (B : ℝ) := Finset.sum_le_sum fun b _ => hcard b
      _ = b0 * B := by simp
  -- piece 3
  have p3 : |∑ n ∈ Finset.range (X - Y * B), f (Y * B + n) - ((X : ℝ) - Y * B) * ℓ| ≤ B := by
    have hcb := sum_card_bounds a0 ℓ (fun n => xf (Y * B + n)) (X - Y * B) hℓ h1
    have : ((X - Y * B : ℕ) : ℝ) = X - Y * B := by rw [Nat.cast_sub hYB]; push_cast; ring
    rw [this] at hcb
    rw [abs_le]; constructor <;> nlinarith
  -- piece 2
  have hbadk : ∀ k' ∈ Finset.range K, ∑ q ∈ Finset.range (Y - b0),
      gfl (-η) (2 * η) (((k' + 1 : ℕ) : ℝ) * Real.logb 10 (((b0 + q) * B : ℕ) : ℝ)) ≤
      2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2 := by
    intro k' hk'
    have := bad_count η B (k' + 1) b0 Y hη0 hηh hB1 (by omega) hb01 hb0Y
    have hk'K : ((k' + 1 : ℕ) : ℝ) ≤ K := by
      exact_mod_cast (by rw [Finset.mem_range] at hk'; omega : k' + 1 ≤ K)
    have : ((k' + 1 : ℕ) : ℝ) * Y / b0 ≤ K * Y / b0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk'K (by positivity)) (by positivity)
    linarith
  have hSsum : ∑ q ∈ Finset.range (Y - b0), S (b0 + q) ≤
      K * (2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2) := by
    simp only [hS]
    rw [Finset.sum_comm]
    calc _ ≤ ∑ k' ∈ Finset.range K, (2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2) :=
          Finset.sum_le_sum hbadk
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have p2 : |∑ q ∈ Finset.range (Y - b0), (Blk (b0 + q) - B * ℓ)| ≤
      Y * G + B * (K * (2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hG0 : 0 ≤ G := by rw [hG]; positivity
    calc _ ≤ ∑ q ∈ Finset.range (Y - b0), (G + B * S (b0 + q)) := Finset.sum_le_sum fun q _ => hcase q
      _ = (Y - b0 : ℕ) * G + B * ∑ q ∈ Finset.range (Y - b0), S (b0 + q) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]; simp
      _ ≤ Y * G + B * (K * (2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2)) := by
          have : ((Y - b0 : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.sub_le Y b0
          have := mul_le_mul_of_nonneg_right this hG0
          have := mul_le_mul_of_nonneg_left hSsum hBR.le
          linarith
  -- numeric bounds
  have hYb0 : (Y : ℝ) / b0 ≤ 1 / ε := by
    rw [div_le_div_iff₀ (by positivity) hε0]; linarith
  have hBX : (B : ℝ) * (2 + K * (K / ε + 2)) ≤ ε * X := by
    have e : (B : ℝ) = L * m := by rw [hB]; push_cast; ring
    rw [e]
    have h := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ m)
    have e2 : (L : ℝ) * m * (2 + K * (K / ε + 2)) = L * (2 + K * (K / ε + 2)) * m := by ring
    have e3 : ε * m * m = ε * (m * m) := by ring
    have : ε * ((m : ℝ) * m) ≤ ε * X := mul_le_mul_of_nonneg_left hXm hε0.le
    linarith
  have hYG : (Y : ℝ) * G ≤ 3 * ε * X := by
    rw [hG]
    have t1 : (Y : ℝ) * B * (2 * τ / η + ε + τ) ≤ X * (2 * ε) := by
      have : 2 * τ / η + ε + τ ≤ 2 * ε := by linarith
      have h0 : 0 ≤ 2 * τ / η + ε + τ := by positivity
      calc (Y : ℝ) * B * (2 * τ / η + ε + τ) ≤ X * (2 * τ / η + ε + τ) :=
            mul_le_mul_of_nonneg_right hYBR h0
        _ ≤ X * (2 * ε) := mul_le_mul_of_nonneg_left this (by positivity)
    have t2 : (Y : ℝ) * (K * (4 / η + 2)) ≤ ε * X := by
      have hY' : (Y : ℝ) ≤ X / (L * m) := by
        rw [le_div_iff₀ (by positivity)]
        have e : (B : ℝ) = L * m := by rw [hB]; push_cast; ring
        rw [← e]; exact hYBR
      calc (Y : ℝ) * (K * (4 / η + 2)) ≤ X / (L * m) * (ε * L * m) :=
            mul_le_mul hY' hd (by positivity) (by positivity)
        _ = ε * X := by field_simp
    have e : (Y : ℝ) * (B * (2 * τ / η + ε + τ) + K * (4 / η + 2)) =
        Y * B * (2 * τ / η + ε + τ) + Y * (K * (4 / η + 2)) := by ring
    rw [e]; linarith
  have hbad : (B : ℝ) * (K * (2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2)) ≤
      6 * ε * X + B * (K * (K / ε + 2)) := by
    have hKη : (K : ℝ) * η = ε ^ 2 := by rw [hη]; field_simp
    have e : (B : ℝ) * (K * (2 * η * Y * (Y / b0) + K * Y / b0 + 14 * η * Y + 2)) =
        (Y * B) * (2 * (K * η) * (Y / b0) + 14 * (K * η)) + B * (K * (K * (Y / b0) + 2)) := by ring
    rw [e, hKη]
    have u1 : 2 * ε ^ 2 * (Y / b0) + 14 * ε ^ 2 ≤ 6 * ε := by
      have : ε ^ 2 * (Y / b0) ≤ ε ^ 2 * (1 / ε) := mul_le_mul_of_nonneg_left hYb0 (by positivity)
      have e2 : ε ^ 2 * (1 / ε) = ε := by field_simp
      have : 14 * ε ^ 2 ≤ 4 * ε := by linarith
      linarith
    have u2 : (Y : ℝ) * B * (2 * ε ^ 2 * (Y / b0) + 14 * ε ^ 2) ≤ X * (6 * ε) :=
      mul_le_mul hYBR u1 (by positivity) (by positivity)
    have u3 : (B : ℝ) * (K * (K * (Y / b0) + 2)) ≤ B * (K * (K / ε + 2)) := by
      apply mul_le_mul_of_nonneg_left _ hBR.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hYb0 (by positivity : (0 : ℝ) ≤ K)
      have e3 : (K : ℝ) * (1 / ε) = K / ε := by ring
      linarith
    linarith
  have hb0B : (b0 : ℝ) * B ≤ ε * X + B := by
    have : (b0 : ℝ) * B ≤ (ε * Y + 1) * B := mul_le_mul_of_nonneg_right hb0b hBR.le
    have e : (ε * Y + 1) * B = ε * (Y * B) + B := by ring
    have : ε * ((Y : ℝ) * B) ≤ ε * X := mul_le_mul_of_nonneg_left hYBR hε0.le
    linarith
  rw [hsplit]
  calc _ ≤ |∑ b ∈ Finset.range b0, (Blk b - B * ℓ)| + |∑ q ∈ Finset.range (Y - b0), (Blk (b0 + q) - B * ℓ)| +
        |∑ n ∈ Finset.range (X - Y * B), f (Y * B + n) - ((X : ℝ) - Y * B) * ℓ| := abs_add_three _ _ _
    _ ≤ 11 * ε * X := by
      have e : (B : ℝ) * (2 + K * (K / ε + 2)) = 2 * B + B * (K * (K / ε + 2)) := by ring
      linarith

end BenfordFac


open Filter Topology BenfordWeyl BenfordLaw

namespace BenfordFac

theorem fac_equidist (a0 ℓ : ℝ) (hℓ : 0 ≤ ℓ) (h1 : ℓ ≤ 1) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range X, gfl a0 ℓ (xf n)) / X) atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop]
  intro ε0 hε0
  set ε := min (ε0 / 12) (1 / 4) with hεdef
  have hε0' : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε : ε ≤ 1 / 4 := min_le_right _ _
  have hεε : ε ≤ ε0 / 12 := min_le_left _ _
  set K := ⌈1 / ε⌉₊ with hKdef
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hKge : 1 / ε ≤ K := Nat.le_ceil _
  have hKε : 1 / ((K : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε0'] at hKge
    nlinarith
  set L := K.factorial with hL
  have hLR : (1 : ℝ) ≤ L := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K)
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set A : ℝ := 3 * K / (ε * (ε ^ 2 / K)) with hA
  set R : ℝ := max (max (3 * L) (L * (A / ε + 1)))
    (max (L * (2 + K * (K / ε + 2)) / ε) (K * (4 / (ε ^ 2 / K) + 2) / (ε * L))) with hR
  set m0 := ⌈R⌉₊ + 1 with hm0
  refine ⟨m0 * m0, fun X hX => ?_⟩
  set m := Nat.sqrt X with hm
  have hmm0 : m0 ≤ m := Nat.le_sqrt.mpr hX
  have hmR : R ≤ m := by
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hmm0
    have : R ≤ m0 := by rw [hm0]; push_cast; linarith [Nat.le_ceil R]
    linarith
  have hm1 : 1 ≤ m := by omega
  have hmX : m * m ≤ X := Nat.sqrt_le X
  have hXpos : (0 : ℝ) < X := by
    have : 1 ≤ X := le_trans (by nlinarith) hmX
    exact_mod_cast this
  have ha : 3 * (L : ℝ) ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmR
  have hb : A ≤ ε * (m / L - 1) := by
    have h := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmR
    have : A / ε + 1 ≤ m / L := by rw [le_div_iff₀ (by positivity)]; linarith
    have : A / ε ≤ m / L - 1 := by linarith
    rw [div_le_iff₀ hε0'] at this; linarith
  have hc : (L : ℝ) * (2 + K * (K / ε + 2)) ≤ ε * m := by
    have h := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmR
    rw [div_le_iff₀ hε0'] at h; linarith
  have hd : (K : ℝ) * (4 / (ε ^ 2 / K) + 2) ≤ ε * L * m := by
    have h := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmR
    rw [div_le_iff₀ (by positivity)] at h; linarith
  have key := main_bound a0 ℓ ε hℓ h1 hε0' hε K hK hKε X m hm1 hmX ha hb hc hd
  rw [Real.dist_eq, show (∑ n ∈ Finset.range X, gfl a0 ℓ (xf n)) / X - ℓ =
      (∑ n ∈ Finset.range X, gfl a0 ℓ (xf n) - X * ℓ) / X by field_simp, abs_div,
    abs_of_pos hXpos, div_lt_iff₀ hXpos]
  have : 11 * ε * X < ε0 * X := by nlinarith
  linarith

end BenfordFac

open BenfordWeyl BenfordFac in
theorem solution : IsBenfordSeq 10 (fun n => ((n + 1).factorial : ℝ)) := by
  intro d hd1 hd10
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd9 : (d : ℝ) + 1 ≤ 10 := by exact_mod_cast (by omega : d + 1 ≤ 10)
  set a0 := Real.logb 10 d with ha0
  set ℓ := benfordProb 10 d with hℓ
  have hℓ_eq : ℓ = Real.logb 10 (d + 1) - a0 := by
    rw [hℓ, benfordProb, ha0, ← Real.logb_div (by positivity) hd0.ne']
    congr 1; field_simp
  have h0 : 0 ≤ a0 := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd1)
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ_eq]; linarith [Real.logb_le_logb_of_le (b := 10) (by norm_num) hd0
      (by linarith : (d : ℝ) ≤ d + 1)]
  have h1 : a0 + ℓ ≤ 1 := by
    rw [hℓ_eq]; ring_nf
    calc Real.logb 10 (1 + d) ≤ Real.logb 10 10 :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
      _ = 1 := Real.logb_self_eq_one (by norm_num)
  have key := fac_equidist a0 ℓ hℓ0 (by linarith)
  refine key.congr fun N => ?_
  unfold digitFreq
  congr 1
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show gfl a0 ℓ (xf n) = ind a0 ℓ (xf n) from (ind_eq a0 ℓ _ h0 hℓ0 h1).symm]
  unfold ind
  refine if_congr ?_ rfl rfl
  symm
  have ha : a0 + ℓ = Real.logb 10 (d + 1) := by rw [hℓ_eq]; ring
  rw [ha]
  unfold leadingDigit xf
  have hb1 : (1 : ℝ) < ((10 : ℕ) : ℝ) := by norm_num
  rw [Nat.floor_eq_iff (by positivity)]
  push_cast at hb1 ⊢
  rw [Real.logb_le_iff_le_rpow hb1 hd0, Real.lt_logb_iff_rpow_lt hb1 (by positivity)]

