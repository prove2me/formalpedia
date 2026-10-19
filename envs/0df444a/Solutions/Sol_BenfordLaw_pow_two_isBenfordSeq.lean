-- Prove2me | solution 1 for BenfordLaw.pow_two_isBenfordSeq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:16:23.516248+00:00
-- url     : https://prove2.me/submissions/570b6374-1844-4000-adaf-200579bfd79a

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

/-- **Equidistribution of `x0 + nθ` modulo 1** for irrational `θ`, tested on intervals. -/
theorem equidist (θ : ℝ) (hθ : Irrational θ) (x0 a0 ℓ : ℝ) (h0 : 0 ≤ a0) (hℓ : 0 ≤ ℓ)
    (h1 : a0 + ℓ ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ind a0 ℓ (x0 + n * θ)) / N) atTop (𝓝 ℓ) := by
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
  set Count := fun N : ℕ => ∑ n ∈ Finset.range N, ind a0 ℓ (x0 + n * θ) with hCount
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
        |∑ q ∈ Finset.range M, ind a0 ℓ (x0 + ((q * k + i : ℕ) : ℝ) * θ) - M * ℓ| ≤
          M * δ + ℓ / δ + 1 := by
      intro i _
      have e : ∀ q : ℕ, ind a0 ℓ (x0 + ((q * k + i : ℕ) : ℝ) * θ) =
          (⌊(x0 + i * θ - a0) + q * δ⌋ : ℝ) - ⌊(x0 + i * θ - a0) - ℓ + q * δ⌋ := by
        intro q
        have : x0 + ((q * k + i : ℕ) : ℝ) * θ =
            (x0 + i * θ + q * δ) + ((q * ⌊(k : ℝ) * θ⌋ : ℤ) : ℝ) := by
          rw [hδ, Int.fract]; push_cast; ring
        rw [this, ind_add_int, ind_eq a0 ℓ _ h0 hℓ h1]
        congr 3 <;> ring
      simp only [e]
      exact prog_bound _ δ ℓ hδ0 hℓ M
    have := Finset.abs_sum_le_sum_abs
      (fun i => ∑ q ∈ Finset.range M, ind a0 ℓ (x0 + ((q * k + i : ℕ) : ℝ) * θ) - M * ℓ)
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
        ∑ n ∈ Finset.range (N - M * k), ind a0 ℓ (x0 + ((M * k + n : ℕ) : ℝ) * θ) := by
      simp only [hCount]
      rw [← Finset.sum_range_add, Nat.add_sub_cancel' hMk1]
    rw [e, add_sub_cancel_left]
    constructor
    · exact Finset.sum_nonneg fun n _ => ind_nonneg _ _ _
    · calc _ ≤ ∑ n ∈ Finset.range (N - M * k), (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => ind_le_one _ _ _
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
  have hℓ1 : ℓ ≤ 1 := by linarith
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

end BenfordWeyl

open BenfordLaw

open BenfordWeyl in
theorem pow_benford (k : ℕ) (hk : Irrational (Real.logb 10 k)) :
    IsBenfordSeq 10 (fun n => (k : ℝ) ^ (n + 1)) := by
  intro d hd1 hd10
  have hk0 : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hk; simp at hk
    · exact_mod_cast h
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd9 : (d : ℝ) + 1 ≤ 10 := by exact_mod_cast (by omega : d + 1 ≤ 10)
  set θ := Real.logb 10 k with hθ
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
  have key := equidist θ hk θ a0 ℓ h0 hℓ0 h1
  refine key.congr fun N => ?_
  unfold digitFreq
  congr 1
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold ind
  refine if_congr ?_ rfl rfl
  have hpos : (0 : ℝ) < (k : ℝ) ^ (n + 1) := by positivity
  have hlog : Real.logb 10 ((k : ℝ) ^ (n + 1)) = θ + n * θ := by
    rw [Real.logb_pow]; push_cast; ring
  have ha : a0 + ℓ = Real.logb 10 (d + 1) := by rw [hℓ_eq]; ring
  rw [ha]
  unfold leadingDigit
  have hb1 : (1 : ℝ) < ((10 : ℕ) : ℝ) := by norm_num
  rw [Nat.floor_eq_iff (by positivity)]
  push_cast at hb1 ⊢
  rw [Real.logb_le_iff_le_rpow hb1 hd0, Real.lt_logb_iff_rpow_lt hb1 (by positivity), hlog]

lemma irrational_logb_ten_two : Irrational (Real.logb 10 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb0 hab
  have hpos : 0 < Real.logb 10 2 := Real.logb_pos (by norm_num) (by norm_num)
  rcases lt_or_gt_of_ne hb0 with hb | hb
  · have hab' : Real.logb 10 2 = ((-a : ℤ) : ℝ) / ((-b : ℤ) : ℝ) := by
      rw [hab]; push_cast; rw [neg_div_neg_eq]
    exact aux (-a) (-b) (by omega) hab' hpos
  · exact aux a b hb hab hpos
where
  aux (a b : ℤ) (hb : 0 < b) (hab : Real.logb 10 2 = (a : ℝ) / b)
      (hpos : 0 < Real.logb 10 2) : False := by
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have ha : 0 < a := by
      have : (0 : ℝ) < a / b := hab ▸ hpos
      have : (0 : ℝ) < a := by
        rcases lt_or_ge (a : ℝ) 0 with h | h
        · exact absurd this (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg h.le hbR.le))
        · rcases h.lt_or_eq with h | h
          · exact h
          · rw [← h] at this; simp at this
      exact_mod_cast this
    have hmul : (b : ℝ) * Real.logb 10 2 = a := by rw [hab]; field_simp
    have h2 : ((2 : ℝ) ^ b.toNat) = (10 : ℝ) ^ a.toNat := by
      have e1 : ((b.toNat : ℕ) : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb.le
      have e2 : ((a.toNat : ℕ) : ℝ) = a := by exact_mod_cast Int.toNat_of_nonneg ha.le
      rw [← e1, ← e2, ← Real.logb_pow] at hmul
      have := congrArg (fun t => (10 : ℝ) ^ t) hmul
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at this
      exact this
    have h3 : (2 : ℕ) ^ b.toNat = 10 ^ a.toNat := by exact_mod_cast h2
    have h5 : 5 ∣ 2 ^ b.toNat := by
      rw [h3]
      exact dvd_pow (by norm_num : 5 ∣ 10) (by omega : a.toNat ≠ 0)
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5)
    omega

open BenfordWeyl in
theorem solution : IsBenfordSeq 10 (fun n => (2 : ℝ) ^ (n + 1)) := by
  have := pow_benford 2 (by exact_mod_cast irrational_logb_ten_two)
  simpa using this
