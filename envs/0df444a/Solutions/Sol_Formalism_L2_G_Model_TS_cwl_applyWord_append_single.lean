-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_applyWord_append_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:50.335996+00:00
-- url     : https://prove2.me/submissions/cbd81816-618d-4fd9-a2ca-f770f7a60fd3

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (w : List (Fin r × Fin r × ℕ)) (x : Fin r × Fin r × ℕ)
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (w ++ [x]) F = applyWord R w (rowDiv R x.1 x.2.1 x.2.2 F) := by
  simp [applyWord, List.foldr_append]
end Formalism.L2.G.Model.TS
