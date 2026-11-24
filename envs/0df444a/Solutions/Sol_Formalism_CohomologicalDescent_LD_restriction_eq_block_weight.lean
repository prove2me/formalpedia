-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.restriction_eq_block_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:07.24745+00:00
-- url     : https://prove2.me/submissions/2032d1f8-52bc-473b-8a67-d73ca6ac0530

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (n t : ℕ) (lam : ℕ → ℕ) (hc : ∀ a, n ≤ a → a < n + t → lam a = lam n) :
    res (n + t) lam = blockWtLast t n (lam n) (res n lam) := by
  funext a
  unfold blockWtLast
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right]
    show lam (Fin.natAdd n b).val = lam n
    rw [Fin.val_natAdd]
    exact hc _ (Nat.le_add_right _ _) (Nat.add_lt_add_left b.isLt n)
end Formalism.CohomologicalDescent.LD
