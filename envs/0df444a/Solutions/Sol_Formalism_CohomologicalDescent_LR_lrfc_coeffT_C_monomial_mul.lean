-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_coeffT_C_monomial_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:32.146842+00:00
-- url     : https://prove2.me/submissions/a4a240c1-7e31-4c6b-bb17-505879d7d912

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeff_coeffT
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
theorem _root_.solution (d s : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_coeffT d (C (monomial s 1) * G) = if s ≤ d then lrfc_coeffT (d - s) G else 0 := by
  classical
  ext m
  rw [lrfc_coeff_coeffT, coeff_C_mul, coeff_monomial_mul', one_mul]
  split_ifs
  · rw [lrfc_coeff_coeffT]
  · simp
end Formalism.CohomologicalDescent.LR
