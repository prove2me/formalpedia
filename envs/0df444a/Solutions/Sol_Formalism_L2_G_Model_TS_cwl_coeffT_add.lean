-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_coeffT_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:47.299852+00:00
-- url     : https://prove2.me/submissions/0f44d8d7-5ce2-47d6-85b1-95ee4f2c1e2a

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeff_coeffT
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
theorem _root_.solution (d : Fin r × Fin n →₀ ℕ)
    (G H : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_coeffT d (G + H) = cwl_coeffT d G + cwl_coeffT d H := by
  ext m
  simp [cwl_coeff_coeffT]
end Formalism.L2.G.Model.TS
