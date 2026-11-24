-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depth2Dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:08.846396+00:00
-- url     : https://prove2.me/submissions/c5ba8134-e29d-4971-b5ea-9b28b1c8b2dd

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
theorem _root_.solution : Depth2Dual := by
  intro r M ξ lam μ hl hm
  constructor
  · unfold depth2
    rw [← Equiv.sum_comp Fin.revPerm fun a => ξ a * ((lam a : ℤ) - (μ a : ℤ))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_sub (hl _), Nat.cast_sub (hm _)]
    simp only [Fin.revPerm_apply]
    ring
  · intro hξ a b hab
    exact neg_le_neg (hξ (Fin.rev_le_rev.mpr hab))
end Formalism.CohomologicalDescent.LD
