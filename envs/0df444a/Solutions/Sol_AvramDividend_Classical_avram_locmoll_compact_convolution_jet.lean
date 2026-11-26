-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_compact_convolution_jet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:43:56.138296+00:00
-- url     : https://prove2.me/submissions/0f61179e-04f4-45e6-b192-cae4f7e75164

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false
theorem solution
    (ρ F : ℝ → ℝ) (hρ : Integrable ρ)
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (y : ℝ) :
    Integrable (fun r => ρ r * F (y - r)) ∧
    Integrable (fun r => ρ r * deriv F (y - r)) ∧
    Integrable (fun r => ρ r * iteratedDeriv 2 F (y - r)) ∧
    deriv (fun t => ∫ r, ρ r * F (t - r)) y =
      (∫ r, ρ r * deriv F (y - r)) ∧
    iteratedDeriv 2 (fun t => ∫ r, ρ r * F (t - r)) y =
      (∫ r, ρ r * iteratedDeriv 2 F (y - r)) := by 
  have hloc : LocallyIntegrable ρ volume := hρ.locallyIntegrable
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hD0 : ContDiff ℝ 0 (deriv (deriv F)) := hD.deriv'
  have hD2 : Continuous (deriv (deriv F)) := hD0.continuous
  have h2 (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd (x : ℝ) : deriv (fun t => ∫ r, ρ r * F (t - r)) x =
      (∫ r, ρ r * deriv F (x - r)) :=
    (hFc.hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hloc hF1 x).deriv
  refine ⟨?_, ?_, ?_, hd y, ?_⟩
  · exact (hFc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      hloc hF.continuous y).integrable
  · exact (hFc.deriv.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      hloc hD.continuous y).integrable
  · rw [h2 F]
    exact (hFc.deriv.deriv.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      hloc hD2 y).integrable
  · rw [h2, h2, funext hd]
    exact (hFc.deriv.hasDerivAt_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hloc hD y).deriv
