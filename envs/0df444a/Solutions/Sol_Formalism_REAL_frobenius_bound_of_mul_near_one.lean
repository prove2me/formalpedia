-- Prove2me | solution 1 for Formalism.REAL.frobenius_bound_of_mul_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:09.877636+00:00
-- url     : https://prove2.me/submissions/4fc49d30-2fe6-4c47-b9e9-39ec6fd7c5aa

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_frobenius_eq_norm_sq
import Theorems.Thm_Formalism_REAL_norm_sub_one_lt_half
import Theorems.Thm_Formalism_REAL_norm_le_of_near_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {k u v : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4)
    (hv : hs (v - 1) < 1 / 4) (h : k * u = v) : hs k ≤ (2 * Real.sqrt n + 1) ^ 2 := by
  have e : k = v + k * (1 - u) := by rw [Matrix.mul_sub, Matrix.mul_one, h]; abel
  have h1 : ‖k‖ ≤ ‖v‖ + ‖k‖ * ‖1 - u‖ := by
    calc ‖k‖ = ‖v + k * (1 - u)‖ := by rw [← e]
      _ ≤ ‖v‖ + ‖k * (1 - u)‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  rw [norm_sub_rev] at h1
  have h2 := norm_sub_one_lt_half hu
  have h3 := norm_le_of_near_one hv
  have hk : ‖k‖ ≤ 2 * Real.sqrt n + 1 := by nlinarith [norm_nonneg k, norm_nonneg (u - 1)]
  rw [frobenius_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hk 2
end Formalism.REAL
