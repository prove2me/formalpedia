-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.sum_block_weight_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:07.303344+00:00
-- url     : https://prove2.me/submissions/8eaa5d6b-2402-4575-8386-d3eca293ea83

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
theorem _root_.solution (p q w : ℕ) (lam2 : Fin q → ℕ) :
    ∑ a, blockWtLast p q w lam2 a = ∑ b, lam2 b + p * w := by
  unfold blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
end Formalism.CohomologicalDescent.LD
