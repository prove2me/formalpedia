-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lre_le_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:29.639888+00:00
-- url     : https://prove2.me/submissions/c09928b6-e86f-4836-a4c3-7a921c91f91f

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution {s r : ℕ} (I : Fin s → Fin r) (hI : StrictMono I) (p : Fin s) : p.val ≤ (I p).val := by
  obtain ⟨k, hk⟩ := p
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 : I ⟨k, by omega⟩ < I ⟨k + 1, hk⟩ := hI (by simp [Fin.lt_def])
    have h3 : (I ⟨k, by omega⟩).val < (I ⟨k + 1, hk⟩).val := h2
    show k + 1 ≤ (I ⟨k + 1, hk⟩).val
    have h1' : k ≤ (I ⟨k, by omega⟩).val := h1
    omega
end Formalism.CohomologicalDescent.LR
