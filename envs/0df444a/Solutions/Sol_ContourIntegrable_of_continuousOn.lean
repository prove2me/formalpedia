-- Prove2me | solution 1 for ContourIntegrable.of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:33:19.469052+00:00
-- url     : https://prove2.me/submissions/e6830436-1589-45c0-80d4-a2dff7825771

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace ContourIntegrable
theorem _root_.solution {f : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 (2 * π))) (hγ' : ContinuousOn (deriv γ) (Icc 0 (2 * π)))
    (hf : ContinuousOn f (γ '' Icc 0 (2 * π))) : ContourIntegrable f γ := by
  unfold ContourIntegrable
  rw [← uIcc_of_le Real.two_pi_pos.le] at hγ hγ' hf
  exact (hγ'.smul (hf.comp hγ (mapsTo_image _ _))).intervalIntegrable
end ContourIntegrable
