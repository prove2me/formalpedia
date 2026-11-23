-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclosedeq_weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:34.85344+00:00
-- url     : https://prove2.me/submissions/9279d402-09e1-4b08-a07a-9328d0024e44

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) :
    ∑ s : Fin n, Finsupp.weight (colW r n) m s = Finsupp.weight (1 : Fin r × Fin n → ℕ) m := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [colW, Pi.single_apply]
end Formalism.GradedWeylDivisibility
