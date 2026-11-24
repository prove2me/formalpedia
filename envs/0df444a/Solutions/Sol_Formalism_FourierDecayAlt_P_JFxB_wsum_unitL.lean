-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.wsum_unitL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:53:58.453494+00:00
-- url     : https://prove2.me/submissions/8f75ec76-4143-44a8-862d-db6d102df27c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (unitL L) f g = wsum L f g := by
  induction L with
  | nil => simp [unitL, wsum]
  | cons cw L ih =>
    simp only [unitL, List.map_cons] at ih ⊢
    rw [wsum_cons, wsum_cons, ih, Rw_scale cw.2 f, mul_smul, smul_comm]
end Formalism.FourierDecayAlt.P.JFxB
