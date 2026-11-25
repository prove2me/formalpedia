-- Prove2me | solution 1 for Formalism.G0.choice_of_tops_refined_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:48.64355+00:00
-- url     : https://prove2.me/submissions/5652a320-458d-43c0-8baf-22082d9226fa

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_or_le_add
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_condProbAt_eq
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_partA
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_partC
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_partB
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono


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
open TopsChoiceProbabilityLemmas TopsConditionalProbabilityWindows
namespace Formalism.G0
theorem _root_.solution : TileConditionFailureProbBound := by
  classical
  intro n δ L₂ K r u M₀ G' N₁ i₀ h0 h1 hr hu hn hi
  have hn1 : 1 ≤ n := by omega
  rw [condProbAt_eq n δ i₀ hi]
  calc P ((range n).erase i₀) δ (fun t => ¬ GoodOrbitIntervalTileCondition n (insert i₀ t) L₂ K r u M₀ G' N₁)
      ≤ P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K ∨
          (¬ CondTiles n (insert i₀ t) r u M₀ ∨ ¬ CondIntervals n (insert i₀ t) G' N₁)) := by
        apply P_mono h0 h1
        intro t _ h
        unfold GoodOrbitIntervalTileCondition at h
        tauto
    _ ≤ P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) +
          P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀ ∨
            ¬ CondIntervals n (insert i₀ t) G' N₁) :=
        prob_or_le_add h0 h1 (fun t => ¬ CondA n (insert i₀ t) L₂ K)
          (fun t => ¬ CondTiles n (insert i₀ t) r u M₀ ∨ ¬ CondIntervals n (insert i₀ t) G' N₁)
    _ ≤ P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) +
          (P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀) +
            P ((range n).erase i₀) δ (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁)) :=
        add_le_add le_rfl (prob_or_le_add h0 h1 (fun t => ¬ CondTiles n (insert i₀ t) r u M₀)
          (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁))
    _ ≤ n * (L₂.choose K : ℝ) * δ ^ K + (n * (1 - markedBound δ r u) ^ M₀ +
          n * binUpper G' δ (N₁ - 1)) :=
        add_le_add (partA n δ h0 h1 L₂ K i₀ hn1)
          (add_le_add (partB h0 h1 hu hn) (partC n δ h0 h1 G' N₁ i₀ hn1))
    _ = _ := by ring
end Formalism.G0
