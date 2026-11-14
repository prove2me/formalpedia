-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_difference_variance_of_self_covariance_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:02:46.991436+00:00
-- url     : https://prove2.me/submissions/5eb7d226-0261-4c10-987f-d2273c3b3f9f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Original-space Gaussian variance algebra under the exact physical covariance. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : Ω → ℝ)
    (hU : Integrable (fun ω => (U ω)^2) P)
    (hV : Integrable (fun ω => (V ω)^2) P)
    (hUV : Integrable (fun ω => U ω * V ω) P)
    (hCov : (∫ ω, U ω * V ω ∂P) = (∫ ω, (V ω)^2 ∂P)) :
    Integrable (fun ω => (U ω - V ω)^2) P ∧
      (∫ ω, (U ω - V ω)^2 ∂P) =
        (∫ ω, (U ω)^2 ∂P) - (∫ ω, (V ω)^2 ∂P) := by
  have hCross : Integrable (fun ω => (2 : ℝ) * (U ω * V ω)) P :=
    hUV.const_mul 2
  have hPoly : (fun ω => (U ω - V ω)^2) =
      (fun ω => (U ω)^2 + (V ω)^2 - 2 * (U ω * V ω)) := by
    funext ω
    ring
  rw [hPoly]
  constructor
  · exact (hU.add hV).sub hCross
  · calc
      (∫ ω, ((U ω)^2 + (V ω)^2 - 2 * (U ω * V ω)) ∂P) =
          (∫ ω, ((U ω)^2 + (V ω)^2) ∂P) -
            (∫ ω, 2 * (U ω * V ω) ∂P) := by
              exact integral_sub (hU.add hV) hCross
      _ = (∫ ω, (U ω)^2 ∂P) - (∫ ω, (V ω)^2 ∂P) := by
        rw [integral_add hU hV, integral_const_mul, hCov]
        ring
