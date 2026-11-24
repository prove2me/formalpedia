-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_coeffT_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:48.238643+00:00
-- url     : https://prove2.me/submissions/f9d34859-3aee-44d0-a137-861739121560

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
theorem _root_.solution (d : Fin r × Fin n →₀ ℕ) (F : MvPolynomial (Fin r × Fin n) R) :
    cwl_coeffT d (cwl_iota F) = if d = 0 then F else 0 := by
  classical
  ext m
  rw [cwl_coeff_coeffT, cwl_iota, coeff_map, coeff_C]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]
end Formalism.L2.G.Model.TS
