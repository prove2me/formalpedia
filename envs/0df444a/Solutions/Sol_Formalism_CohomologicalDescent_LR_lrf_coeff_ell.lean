-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_coeff_ell
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:18.253632+00:00
-- url     : https://prove2.me/submissions/6a66564b-55a1-4bc6-a95f-a2ca6200e8b5

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_prod_lower
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_prod_upper
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_unique
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_weight_colW_apply
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
theorem _root_.solution (ν : Fin n → ℕ) (F : MvPolynomial (Fin r × Fin n) R) (e : Fin r × Fin n →₀ ℕ)
    (hF : IsWeightedHomogeneous (colW r n) F ν) (he : LowerTri e) (hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s) :
    coeff (lrf_off e) (eval₂ C (lrf_ell R r n) F) = coeff e F := by
  classical
  rw [eval₂_eq', coeff_sum]
  have key : ∀ m ∈ F.support, coeff (lrf_off e) (C (coeff m F) * ∏ i, lrf_ell R r n i ^ m i) =
      if m = e then coeff m F else 0 := by
    intro m hm
    have hp : (∏ i, lrf_ell R r n i ^ m i) = m.prod fun v k => lrf_ell R r n v ^ k := by
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rw [hp, coeff_C_mul]
    by_cases hl : LowerTri m
    · rw [lrf_prod_lower m hl, coeff_monomial]
      by_cases hme : m = e
      · subst hme
        simp
      · rw [if_neg hme, if_neg, mul_zero]
        intro hoff
        apply hme
        refine lrf_unique m e hl he hoff fun s => ?_
        rw [hcol s, ← lccomp_weight_colW_apply, hF (mem_support_iff.mp hm)]
    · rw [lrf_prod_upper m hl, coeff_zero, mul_zero, if_neg]
      rintro rfl
      exact hl he
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (notMem_support_iff.mp h).symm
end Formalism.CohomologicalDescent.LR
