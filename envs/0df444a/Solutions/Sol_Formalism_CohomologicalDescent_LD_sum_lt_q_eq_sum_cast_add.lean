-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.sum_lt_q_eq_sum_cast_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:30.489239+00:00
-- url     : https://prove2.me/submissions/7d2677bf-51be-4938-bfc6-909dc400eaaa

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (p q : ℕ) (f : Fin (q + p) → ℕ) :
    (∑ a : Fin (q + p) with a.val < q, f a) = ∑ b : Fin q, f (Fin.castAdd p b) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp
end Formalism.CohomologicalDescent.LD
