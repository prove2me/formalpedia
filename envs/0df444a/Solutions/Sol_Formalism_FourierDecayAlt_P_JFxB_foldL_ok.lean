-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.foldL_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:33.034839+00:00
-- url     : https://prove2.me/submissions/7f15b312-846d-4194-83d8-fed880c34036

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_stepL_ok
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
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) : WOK (foldL k r ts) ts.length := by
  induction ts with
  | nil =>
    intro cw hcw
    simp [foldL] at hcw
    subst hcw
    simp
  | cons t ts ih =>
    simpa [foldL, List.foldr_cons] using stepL_ok (u := t.1) (c := t.2.1) (d := t.2.2) ih
end Formalism.FourierDecayAlt.P.JFxB
