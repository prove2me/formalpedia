-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_eval_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:11.194642+00:00
-- url     : https://prove2.me/submissions/295b1d57-85d4-4425-920a-593c621a4731

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_Phi_cons
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_eval_tau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_Phi L G) = eval (L.foldl (fun y l => cwUpd l y) y) G := by
  induction L generalizing y with
  | nil => rfl
  | cons l w ih => rw [cwl_Phi_cons, cw_eval_tau, ih]; rfl
end Formalism.L2.G.Model.TS
