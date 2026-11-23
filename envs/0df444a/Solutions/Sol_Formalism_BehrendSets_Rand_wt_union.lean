-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.wt_union
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:40.910016+00:00
-- url     : https://prove2.me/submissions/23f4de2e-1cc4-4e17-b947-82a29cc8dc66

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Rand
theorem _root_.solution (X S U : Finset α) (δ : ℝ) (hU : U ⊆ X \ S) :
    wt X δ (S ∪ U) = δ ^ S.card * wt (X \ S) δ U := by
  unfold wt
  have hd : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (mem_sdiff.mp (hU hb)).2 ha
  have he : X \ (S ∪ U) = (X \ S) \ U := by
    ext a
    simp only [mem_sdiff, mem_union]
    tauto
  rw [card_union_of_disjoint hd, pow_add, he, mul_assoc]
end Formalism.BehrendSets.Rand
