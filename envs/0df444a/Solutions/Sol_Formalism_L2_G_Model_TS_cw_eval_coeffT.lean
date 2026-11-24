-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_eval_coeffT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:52.289803+00:00
-- url     : https://prove2.me/submissions/e5124762-2d70-4d28-917a-c437c0ec7110

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_add
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_monomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution (d : Fin r × Fin n →₀ ℕ) (y : Fin r × Fin n → R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_coeffT d G) = coeff d (eval (fun v => C (y v)) G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [cwl_coeffT_monomial, eval_monomial, eval_monomial]
    have h : (u.prod fun v k => (C (y v) : MvPolynomial (Fin r × Fin n) R) ^ k) =
        C (u.prod fun v k => y v ^ k) := by
      simp [Finsupp.prod, map_prod]
    rw [h, mul_comm c, coeff_C_mul, mul_comm]
  | add p q hp hq => rw [cwl_coeffT_add, map_add, map_add, coeff_add, hp, hq]
end Formalism.L2.G.Model.TS
