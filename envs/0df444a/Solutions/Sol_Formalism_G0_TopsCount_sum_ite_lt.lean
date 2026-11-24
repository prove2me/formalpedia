-- Prove2me | solution 1 for Formalism.G0.TopsCount.sum_ite_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:43.117512+00:00
-- url     : https://prove2.me/submissions/254b5d2f-1f13-4737-8501-6777f6e1ce50

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsCount
namespace Formalism.G0.TopsCount
theorem _root_.solution (m : ℕ) (δ : ℝ) (K : ℕ) :
    ∑ j ∈ range (m + 1), (if j < K then a m δ j else 0) = A m δ K := by
  rw [← sum_filter]
  unfold A
  apply sum_subset
  · intro j hj
    simp only [mem_filter] at hj
    exact mem_range.2 hj.2
  · intro j hjK hj
    simp only [mem_filter, mem_range, not_and] at hj
    have : m < j := by
      by_contra h
      exact hj (by omega) (mem_range.1 hjK)
    unfold a
    rw [Nat.choose_eq_zero_of_lt this]
    simp
end Formalism.G0.TopsCount
