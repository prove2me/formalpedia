-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_eval_coeffT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:18.28099+00:00
-- url     : https://prove2.me/submissions/9f774080-123a-4f0b-8c6f-6ab19434faab

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_add
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_monomial
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (d : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval (idFrame R r n) (lrfc_coeffT d G) = coeff d (eval (lrf_idS R r n) G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [lrfc_coeffT_monomial, eval_monomial, eval_monomial]
    have h : (u.prod fun i k => lrf_idS R r n i ^ k) = C (u.prod fun i k => idFrame R r n i ^ k) := by
      simp only [lrf_idS, Finsupp.prod, map_prod, map_pow]
    rw [h, mul_comm c, coeff_C_mul, mul_comm]
  | add p q hp hq => rw [lrfc_coeffT_add, map_add, map_add, coeff_add, hp, hq]
end Formalism.CohomologicalDescent.LR
