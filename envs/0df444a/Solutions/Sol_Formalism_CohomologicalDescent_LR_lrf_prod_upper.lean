-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_prod_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:29.979797+00:00
-- url     : https://prove2.me/submissions/ddadc9ed-a959-44fb-876f-bb0adf0c2b14

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
theorem _root_.solution (m : Fin r × Fin n →₀ ℕ) (hm : ¬ LowerTri m) :
    (m.prod fun v k => lrf_ell R r n v ^ k) = 0 := by
  classical
  unfold LowerTri at hm
  push Not at hm
  obtain ⟨a, s, has, hne⟩ := hm
  refine Finset.prod_eq_zero (i := (a, s)) (Finsupp.mem_support_iff.mpr hne) ?_
  have h4 : ¬ a.val = s.val := by omega
  have h6 : ¬ s.val < a.val := by omega
  have h5 : lrf_ell R r n (a, s) = 0 := by simp [lrf_ell, idFrame, h4, h6]
  beta_reduce
  rw [h5, zero_pow hne]
end Formalism.CohomologicalDescent.LR
