-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehw_weight_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:22.082054+00:00
-- url     : https://prove2.me/submissions/3c23b4e7-e371-4ee8-9bfe-19acbe287216

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
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
theorem _root_.solution {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lehwP a) m = ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [rowDeg, lehwP]
  by_cases h : a'.val ≤ a.val
  · simp [h, show a'.val < a.val + 1 by omega]
  · simp [h, show ¬ a'.val < a.val + 1 by omega]
end Formalism.GradedWeylDivisibility
