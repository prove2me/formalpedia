-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depth_two_block_eq_sum_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:37.396203+00:00
-- url     : https://prove2.me/submissions/8609c1a5-7af9-4216-befa-40ed11cdf583

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
theorem _root_.solution (p q w : ℕ) (lam2 : Fin q → ℕ) (μ : Fin (q + p) → ℕ) :
    depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ =
      ((∑ b, lam2 b : ℕ) : ℤ) - ((∑ b : Fin q, μ (Fin.castAdd p b) : ℕ) : ℤ) := by
  unfold depth2 blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Finset.sum_sub_distrib]
end Formalism.CohomologicalDescent.LD
