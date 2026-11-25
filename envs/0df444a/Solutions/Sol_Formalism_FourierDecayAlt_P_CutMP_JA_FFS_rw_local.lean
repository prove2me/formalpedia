-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:23.556436+00:00
-- url     : https://prove2.me/submissions/ec4bb2ae-519b-4b6d-bbaa-012209b804f8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableGerm
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_rdV_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
