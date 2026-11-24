-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_prod_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:29.674092+00:00
-- url     : https://prove2.me/submissions/f577732a-c232-4371-a765-85ef4189bc6e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
theorem _root_.solution (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) :
    (m.prod fun v k => lrf_ell R r n v ^ k) = monomial (lrf_off m) 1 := by
  classical
  rw [← Finsupp.prod_filter_mul_prod_filter_not (fun v : Fin r × Fin n => v.2.val < v.1.val)]
  have h2 : ((m.filter fun v : Fin r × Fin n => ¬ v.2.val < v.1.val).prod fun v k => lrf_ell R r n v ^ k) = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    rw [Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff] at hv
    have h3 : ¬ v.1.val < v.2.val := fun h => hv.1 (hm v.1 v.2 h)
    have h4 : v.1.val = v.2.val := by omega
    have h5 : lrf_ell R r n v = 1 := by simp [lrf_ell, idFrame, h4]
    beta_reduce
    rw [h5, one_pow]
  have h1 : ((m.filter fun v : Fin r × Fin n => v.2.val < v.1.val).prod fun v k => lrf_ell R r n v ^ k) =
      (m.filter fun v : Fin r × Fin n => v.2.val < v.1.val).prod fun v k => (X v : MvPolynomial (Fin r × Fin n) R) ^ k := by
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at hv
    have h4 : ¬ v.1.val = v.2.val := by omega
    have h5 : lrf_ell R r n v = X v := by simp [lrf_ell, idFrame, h4, hv.2]
    beta_reduce
    rw [h5]
  rw [h1, h2, mul_one, lrf_off, monomial_eq, C_1, one_mul]
end Formalism.CohomologicalDescent.LR
