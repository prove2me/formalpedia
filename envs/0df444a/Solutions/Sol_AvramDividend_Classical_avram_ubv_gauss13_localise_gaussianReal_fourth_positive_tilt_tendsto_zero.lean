-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:14:05.58821+00:00
-- url     : https://prove2.me/submissions/c8fd46a9-bec6-45a0-8ea6-6d7e15bb3df9

import Mathlib.Probability.Distributions.Gaussian.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The fourth Gaussian exponentially tilted moment is continuous at zero,
    by differentiability of the fourth derivative of the Gaussian MGF. -/
theorem solution (t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      ∫ z : ℝ, z ^ 4 * Real.exp ((1 / ((n : ℝ) + 1)) * z)
        ∂(gaussianReal 0 t)) atTop
      (𝓝 (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t))) := by
  let θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hIn (u : ℝ) :
      u ∈ interior (integrableExpSet id (gaussianReal 0 t)) := by
    simp [integrableExpSet_id_gaussianReal]
  have hθ : Tendsto θ atTop (𝓝 (0 : ℝ)) := by
    simpa only [θ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hContinuous :
      ContinuousAt (iteratedDeriv 4 (mgf id (gaussianReal 0 t))) 0 :=
    (hasDerivAt_iteratedDeriv_mgf (hIn 0) 4).continuousAt
  have hLimit : Tendsto
      (fun n => iteratedDeriv 4 (mgf id (gaussianReal 0 t)) (θ n))
      atTop (𝓝 (iteratedDeriv 4 (mgf id (gaussianReal 0 t)) 0)) :=
    hContinuous.tendsto.comp hθ
  have hEach (n : ℕ) :
      (∫ z : ℝ, z ^ 4 * Real.exp (θ n * z)
        ∂(gaussianReal 0 t)) =
        iteratedDeriv 4 (mgf id (gaussianReal 0 t)) (θ n) := by
    exact (iteratedDeriv_mgf (hIn (θ n)) 4).symm
  have hZero :
      (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t)) =
        iteratedDeriv 4 (mgf id (gaussianReal 0 t)) 0 := by
    simpa using (iteratedDeriv_mgf_zero (hIn 0) 4).symm
  change Tendsto (fun n : ℕ =>
      ∫ z : ℝ, z ^ 4 * Real.exp (θ n * z)
        ∂(gaussianReal 0 t)) atTop
      (𝓝 (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t)))
  rw [hZero]
  convert hLimit using 1
  funext n
  exact hEach n
