-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.condProbAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:26.55195+00:00
-- url     : https://prove2.me/submissions/542a43a6-e3ae-4f08-a290-9db5ada90cb0

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

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
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution (n : ℕ) (δ : ℝ) (i₀ : ℕ) (hi : i₀ < n) (A : Finset ℕ → Prop) :
    condProbAt n δ i₀ A = P ((range n).erase i₀) δ (fun t => A (insert i₀ t)) := by
  classical
  have h0 : i₀ ∈ range n := mem_range.2 hi
  have hU : range n = insert i₀ ((range n).erase i₀) := (insert_erase h0).symm
  have hc : ((range n).erase i₀).card = n - 1 := by rw [card_erase_of_mem h0, card_range]
  unfold condProbAt P
  conv_lhs => rw [hU]
  rw [sum_powerset_insert (notMem_erase i₀ _)]
  rw [sum_eq_zero (fun t ht => ?_), zero_add]
  · apply sum_congr rfl
    intro t ht
    have h0t : i₀ ∉ t := fun h => notMem_erase i₀ (range n) (mem_powerset.1 ht h)
    have hnt : n - (t.card + 1) = n - 1 - t.card := by omega
    rw [card_insert_of_notMem h0t, hc, hnt]
    by_cases hA : A (insert i₀ t)
    · rw [if_pos ⟨mem_insert_self i₀ t, hA⟩, if_pos hA]
      simp
    · rw [if_neg (fun h => hA h.2), if_neg hA]
  · have h0t : i₀ ∉ t := fun h => notMem_erase i₀ (range n) (mem_powerset.1 ht h)
    rw [if_neg (fun h => h0t h.1)]
end Formalism.G0.TopsChoiceProbabilityLemmas
