-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_coeffT_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:32.798112+00:00
-- url     : https://prove2.me/submissions/b66955c6-34ed-4d64-b3bf-0a9bf9975bd5

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
theorem _root_.solution (d u : Fin r × Fin n →₀ ℕ) (c : MvPolynomial (Fin r × Fin n) R) :
    lrfc_coeffT d (monomial u c) = monomial u (coeff d c) := by
  classical
  ext m
  rw [lrfc_coeff_coeffT, coeff_monomial, coeff_monomial]
  split_ifs <;> simp
end Formalism.CohomologicalDescent.LR
