-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_past_weighted_poisson_count_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:50:24.173991+00:00
-- url     : https://prove2.me/submissions/66ac981d-eeda-498a-8ea0-25b6a961dbe7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

/-- The compensated Poisson count has the exact predictable weighted
quadratic energy, with both variance and integrability derived from the
Poisson PMF and independent past weight. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω → ℝ) (hHm : Measurable H)
    (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hIndep : IndepFun H K P) :
    Integrable (fun ω => (H ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) P ∧
      (∫ ω, (H ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
        (r : ℝ) * ∫ ω, H ω ^ 2 ∂P := by
  have hVariance :=
    AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum r
  let f : ℕ → ℝ := fun n => ((n : ℝ) - (r : ℝ)) ^ 2
  have hfMeas : Measurable f := by fun_prop
  have hfInt : Integrable f (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    refine hVariance.summable.congr (fun n => ?_)
    simp only [f, Real.norm_of_nonneg (sq_nonneg _)]
    rw [poissonMeasure_real_singleton]
    ring
  have hfMean : (∫ n, f n ∂poissonMeasure r) = (r : ℝ) := by
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    refine (tsum_congr (fun n => ?_)).trans hVariance.tsum_eq
    rw [poissonMeasure_real_singleton]
    ring
  have hKInt : Integrable (fun ω => f (K ω)) P := by
    have hfMap : Integrable f (Measure.map K P) := by
      rwa [hKlaw.map_eq]
    exact hfMap.comp_measurable hKm
  have hKMean : (∫ ω, f (K ω) ∂P) = (r : ℝ) := by
    simpa [Function.comp_def] using (hKlaw.integral_comp hfMeas.aestronglyMeasurable).trans hfMean
  have hIndepSq : IndepFun (fun ω => H ω ^ 2) (fun ω => f (K ω)) P := by
    simpa [Function.comp_def, f] using
      hIndep.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2)) hfMeas
  have hProdInt : Integrable
      (fun ω => H ω ^ 2 * f (K ω)) P := by
    have h := hIndepSq.integrable_mul hH2 hKInt
    have hEq : (fun ω => H ω ^ 2 * f (K ω)) =
        (fun ω => H ω ^ 2) * (fun ω => f (K ω)) := by
      funext ω
      rfl
    rw [hEq]
    exact h
  have hProdMean :
      (∫ ω, H ω ^ 2 * f (K ω) ∂P) =
        (∫ ω, H ω ^ 2 ∂P) * (∫ ω, f (K ω) ∂P) := by
    simpa only [Pi.mul_apply] using
      hIndepSq.integral_fun_mul_eq_mul_integral
        hH2.aestronglyMeasurable hKInt.aestronglyMeasurable
  have hSquare :
      (fun ω => (H ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) =
        (fun ω => H ω ^ 2 * f (K ω)) := by
    funext ω
    dsimp [f]
    ring
  constructor
  · rw [hSquare]
    exact hProdInt
  · rw [hSquare, hProdMean, hKMean]
    ring

