-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_N_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:09.613879+00:00
-- url     : https://prove2.me/submissions/8d3f0ea3-c07b-4f04-942b-d8aa36e02d16

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} {L : (Fin d → ℂ) →L[ℂ] ℂ} (hL : L ≠ 0) :
    0 < ∑ l, Complex.normSq (L (Pi.single l 1)) := by
  have h := bkb_sq_le L
  have h1 : 0 < ‖L‖ ^ 2 := by positivity
  by_contra hc
  have h2 : ∑ l, Complex.normSq (L (Pi.single l 1)) ≤ 0 := not_lt.mp hc
  have : (d : ℝ) * ∑ l, Complex.normSq (L (Pi.single l 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) h2
  linarith
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
