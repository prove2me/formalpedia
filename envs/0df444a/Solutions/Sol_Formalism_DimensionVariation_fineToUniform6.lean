-- Prove2me | solution 1 for Formalism.DimensionVariation.fineToUniform6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:50:53.391275+00:00
-- url     : https://prove2.me/submissions/f98a6d7d-6bdc-49ef-8eda-f69f8718dd8c

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution (x eps B0 Nc m c' : ℝ) (hx : 1 ≤ x) (hB : 0 ≤ B0) (hN : 0 ≤ Nc) (hm : 0 ≤ m)
    (h1 : c' ≤ x ^ eps) (h2 : c' * Real.log x ^ 2 ≤ x ^ (2 * eps)) :
    c' * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) ≤ m * (B0 + Nc) * x ^ (2 * eps) := by
  have e : x ^ (2 * eps) = x ^ eps * x ^ eps := by
    rw [two_mul, Real.rpow_add (by linarith)]
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have a1 : c' * (x ^ eps * B0) ≤ x ^ (2 * eps) * B0 := by
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hxe hB)]
  have a2 : c' * (Real.log x ^ 2 * Nc) ≤ x ^ (2 * eps) * Nc := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hN]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add a1 a2) hm]
end Formalism.DimensionVariation
