-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_step_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:58.246806+00:00
-- url     : https://prove2.me/submissions/614dc957-894a-4a3c-b43a-6dc8dd8ad8e1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type*} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) (a : Fin r) (j : Fin n) :
    highestWeightLineUpdate p q x (a, j) =
      (if p < a then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by
  simp only [highestWeightLineUpdate, lhwline_mcol, lhwline_mrow, Finset.mem_filter, Finset.mem_univ,
    true_and, lt_self_iff_false, if_false]
  split_ifs <;> ring
end Formalism.GradedWeylDivisibility
