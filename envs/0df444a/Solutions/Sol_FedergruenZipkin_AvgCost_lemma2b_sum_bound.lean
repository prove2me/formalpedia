-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.lemma2b_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:07:31.295673+00:00
-- url     : https://prove2.me/submissions/26409b1b-560f-454b-aa64-56e350da6cff

import Mathlib

set_option autoImplicit false

namespace P74d022da

/-- The telescoping majorant. -/
noncomputable def F (a r x : ℝ) : ℝ :=
  1 / x + (r + 2 * a) / (2 * x ^ 2) + (r * a + a ^ 2) / (3 * x ^ 3)

lemma key (a r x : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hx : 0 < x) :
    ((x + 1 + a) ^ 2 + r * (x + 1 + a)) / (x + 1) ^ 4 ≤ F a r x - F a r (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have e : F a r x - F a r (x + 1) - ((x + 1 + a) ^ 2 + r * (x + 1 + a)) / (x + 1) ^ 4
      = 1 / (x * (x + 1) ^ 2) + (r + 2 * a) * (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3)
        + (r * a + a ^ 2) * (6 * x ^ 2 + 4 * x + 1) / (3 * x ^ 3 * (x + 1) ^ 4) := by
    unfold F
    field_simp
    ring
  have : 0 ≤ 1 / (x * (x + 1) ^ 2) + (r + 2 * a) * (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3)
        + (r * a + a ^ 2) * (6 * x ^ 2 + 4 * x + 1) / (3 * x ^ 3 * (x + 1) ^ 4) := by
    positivity
  linarith

lemma tendsto_F (a r d : ℝ) :
    Filter.Tendsto (fun N : ℕ => F a r (d + N)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun N : ℕ => (d + (N : ℝ))) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hi : Filter.Tendsto (fun N : ℕ => (d + (N : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h
  have : Filter.Tendsto (fun N : ℕ => (d + (N : ℝ))⁻¹ + (r + 2 * a) / 2 * ((d + (N : ℝ))⁻¹) ^ 2
      + (r * a + a ^ 2) / 3 * ((d + (N : ℝ))⁻¹) ^ 3) Filter.atTop
      (nhds (0 + (r + 2 * a) / 2 * 0 ^ 2 + (r * a + a ^ 2) / 3 * 0 ^ 3)) := by
    exact ((hi.add ((hi.pow 2).const_mul _)).add ((hi.pow 3).const_mul _))
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_pow (by norm_num : (3:ℕ) ≠ 0),
    mul_zero, add_zero] at this
  refine this.congr (fun N => ?_)
  unfold F
  field_simp

lemma hasSum_tel (a r d : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hd : 0 < d) :
    HasSum (fun n : ℕ => F a r (d + n) - F a r (d + (n + 1 : ℕ))) (F a r d) := by
  have hnn : ∀ n : ℕ, 0 ≤ F a r (d + n) - F a r (d + (n + 1 : ℕ)) := by
    intro n
    have hx : 0 < d + n := by positivity
    have := key a r (d + n) ha hr hx
    have h2 : 0 ≤ ((d + n + 1 + a) ^ 2 + r * (d + n + 1 + a)) / (d + n + 1) ^ 4 := by positivity
    have e : d + ((n + 1 : ℕ) : ℝ) = d + n + 1 := by push_cast; ring
    rw [e]
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have e : ∀ N : ℕ, ∑ i ∈ Finset.range N, (F a r (d + i) - F a r (d + (i + 1 : ℕ)))
      = F a r d - F a r (d + N) := by
    intro N
    have := Finset.sum_range_sub' (fun i : ℕ => F a r (d + i)) N
    simpa using this
  simp_rw [e]
  have := (tendsto_F a r d).const_sub (F a r d)
  simpa using this

end P74d022da

theorem solution (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (k : ℤ) (hk : a < k) :
    Summable (fun n : ℕ => (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) /
        ((k : ℝ) + 1 + n - a) ^ 4) ∧
      ∑' n : ℕ, (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) / ((k : ℝ) + 1 + n - a) ^ 4 ≤
        1 / ((k : ℝ) - a) + (r + 2 * a) / (2 * ((k : ℝ) - a) ^ 2) +
          (r * a + a ^ 2) / (3 * ((k : ℝ) - a) ^ 3) := by
  set d : ℝ := (k : ℝ) - a with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hT := P74d022da.hasSum_tel a r d ha hr hd
  have hle : ∀ n : ℕ, (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) /
        ((k : ℝ) + 1 + n - a) ^ 4 ≤ P74d022da.F a r (d + n) - P74d022da.F a r (d + (n + 1 : ℕ)) := by
    intro n
    have hx : 0 < d + n := by positivity
    have h := P74d022da.key a r (d + n) ha hr hx
    have e1 : (k : ℝ) + 1 + n = d + n + 1 + a := by rw [hd_def]; ring
    have e2 : (k : ℝ) + 1 + n - a = d + n + 1 := by rw [hd_def]; ring
    have e3 : d + ((n + 1 : ℕ) : ℝ) = d + n + 1 := by push_cast; ring
    rw [e2, e1, e3]
    exact h
  have hnn : ∀ n : ℕ, 0 ≤ (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) /
        ((k : ℝ) + 1 + n - a) ^ 4 := by
    intro n
    have e1 : (k : ℝ) + 1 + n = d + n + 1 + a := by rw [hd_def]; ring
    have e2 : (k : ℝ) + 1 + n - a = d + n + 1 := by rw [hd_def]; ring
    rw [e2, e1]
    have : 0 < d + n := by positivity
    positivity
  have hS : Summable (fun n : ℕ => (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) /
        ((k : ℝ) + 1 + n - a) ^ 4) :=
    Summable.of_nonneg_of_le hnn hle hT.summable
  refine ⟨hS, ?_⟩
  have := hasSum_le hle hS.hasSum hT
  simpa [P74d022da.F] using this
