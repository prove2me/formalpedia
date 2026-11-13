-- Prove2me | solution 1 for CountingLLL.RandomRAM.reciprocal_cross_series
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:47:31.114987+00:00
-- url     : https://prove2.me/submissions/60f911dc-8b3e-4615-a7cc-719a03e15144

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_prefix_cross_moments

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Summability and evaluation of the upper-triangular cross moments in Lemma 5.4. -/
theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) :
    let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
    let M : ℝ := ∫ x, x ^ 2 ∂ν
    let r : ℝ := ∫ x, x ∂ν
    let q : ℝ := ∫ x, |x| ∂ν
    let C : ℕ × ℕ → ℝ := fun ij => ∫ ω,
      (∏ k ∈ Finset.range ij.1, ω k) * (∏ k ∈ Finset.range (ij.1 + ij.2), ω k) ∂μ
    let A : ℕ × ℕ → ℝ := fun ij => ∫ ω,
      |(∏ k ∈ Finset.range ij.1, ω k) * (∏ k ∈ Finset.range (ij.1 + ij.2), ω k)| ∂μ
    Summable A ∧ Summable C ∧
    (∑' ij, A ij) = (1 - M)⁻¹ * (1 - q)⁻¹ ∧
    (∑' ij, C ij) = (1 - M)⁻¹ * (1 - r)⁻¹ ∧
    2 * (∑' ij, C ij) - (1 - M)⁻¹ = (1 + r) / ((1 - r) * (1 - M)) := by
  dsimp only
  let M : ℝ := ∫ x, x ^ 2 ∂ν
  let r : ℝ := ∫ x, x ∂ν
  let q : ℝ := ∫ x, |x| ∂ν
  have hM0 : 0 ≤ M := integral_nonneg (fun x => sq_nonneg x)
  have hq0 : 0 ≤ q := integral_nonneg (fun x => abs_nonneg x)
  have hqvar := variance_nonneg (fun x : ℝ => ‖x‖) ν
  rw [variance_eq_sub hν.norm] at hqvar
  simp only [Pi.pow_apply, Real.norm_eq_abs, sq_abs] at hqvar
  have hq1 : q < 1 := by dsimp [q, M] at *; nlinarith
  have hsumM : Summable (fun n : ℕ => M ^ n) := summable_geometric_of_lt_one hM0 hM
  have hsumq : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hsumr : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hA : Summable (fun ij : ℕ × ℕ => M ^ ij.1 * q ^ ij.2) :=
    hsumM.mul_of_nonneg hsumq (fun n => pow_nonneg hM0 n) (fun n => pow_nonneg hq0 n)
  have hC : Summable (fun ij : ℕ × ℕ => M ^ ij.1 * r ^ ij.2) :=
    hsumM.mul_of_nonneg hsumr (fun n => pow_nonneg hM0 n) (fun n => pow_nonneg hr0 n)
  have haeq : (fun ij : ℕ × ℕ => ∫ ω,
      |(∏ k ∈ Finset.range ij.1, ω k) * (∏ k ∈ Finset.range (ij.1 + ij.2), ω k)|
      ∂(Measure.infinitePi fun _ : ℕ => ν)) = fun ij => M ^ ij.1 * q ^ ij.2 := by
    funext ij
    exact (CountingLLL.RandomRAM.reciprocal_prefix_cross_moments ν hν ij.1 ij.2).2.2
  have hceq : (fun ij : ℕ × ℕ => ∫ ω,
      (∏ k ∈ Finset.range ij.1, ω k) * (∏ k ∈ Finset.range (ij.1 + ij.2), ω k)
      ∂(Measure.infinitePi fun _ : ℕ => ν)) = fun ij => M ^ ij.1 * r ^ ij.2 := by
    funext ij
    exact (CountingLLL.RandomRAM.reciprocal_prefix_cross_moments ν hν ij.1 ij.2).2.1
  rw [haeq, hceq]
  have hta : (∑' ij : ℕ × ℕ, M ^ ij.1 * q ^ ij.2) = (1 - M)⁻¹ * (1 - q)⁻¹ := by
    rw [hA.tsum_prod]
    simp_rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one hq0 hq1, tsum_mul_right, tsum_geometric_of_lt_one hM0 hM]
  have htc : (∑' ij : ℕ × ℕ, M ^ ij.1 * r ^ ij.2) = (1 - M)⁻¹ * (1 - r)⁻¹ := by
    rw [hC.tsum_prod]
    simp_rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one hr0 hr1, tsum_mul_right, tsum_geometric_of_lt_one hM0 hM]
  refine ⟨hA, hC, hta, htc, ?_⟩
  rw [htc]
  change 2 * ((1 - M)⁻¹ * (1 - r)⁻¹) - (1 - M)⁻¹ = (1 + r) / ((1 - r) * (1 - M))
  have hMne : 1 - M ≠ 0 := by linarith
  have hrne : 1 - r ≠ 0 := by linarith
  field_simp
  <;> ring
