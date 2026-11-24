-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.condProb_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:42.571233+00:00
-- url     : https://prove2.me/submissions/ff0f881a-c016-4951-99fb-ae9578c8d0f9

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (A : Finset ℕ → Prop) :
    condProb n δ A = P ((range n).erase 0) δ (fun t => A (insert 0 t)) := by
  classical
  have h0 : 0 ∈ range n := mem_range.2 hn
  have hU : range n = insert 0 ((range n).erase 0) := (insert_erase h0).symm
  have hc : ((range n).erase 0).card = n - 1 := by rw [card_erase_of_mem h0, card_range]
  unfold condProb P
  conv_lhs => rw [hU]
  rw [sum_powerset_insert (notMem_erase 0 _)]
  rw [sum_eq_zero (fun t ht => ?_), zero_add]
  · apply sum_congr rfl
    intro t ht
    have h0t : 0 ∉ t := fun h => notMem_erase 0 (range n) (mem_powerset.1 ht h)
    have hnt : n - (t.card + 1) = n - 1 - t.card := by omega
    rw [card_insert_of_notMem h0t, hc, hnt]
    by_cases hA : A (insert 0 t)
    · rw [if_pos ⟨mem_insert_self 0 t, hA⟩, if_pos hA]
      simp
    · rw [if_neg (fun h => hA h.2), if_neg hA]
  · have h0t : 0 ∉ t := fun h => notMem_erase 0 (range n) (mem_powerset.1 ht h)
    rw [if_neg (fun h => h0t h.1)]
end Formalism.G0.TopsConditionalProbabilityWindows
