-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.cell_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:34.884336+00:00
-- url     : https://prove2.me/submissions/4463e815-6900-47f1-b081-4458c02faa9b

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_eq

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
theorem _root_.solution {r u s c c' : ℕ} (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : c ≠ c') :
    Disjoint (cell r u s c) (cell r u s c') := by
  rw [cell_eq hc, cell_eq hc']
  rcases lt_or_gt_of_ne h with h | h
  · have : (c - 1) * u + u ≤ (c' - 1) * u := by
      have := Nat.mul_le_mul_right u (show c - 1 + 1 ≤ c' - 1 by omega)
      rwa [add_mul, one_mul] at this
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega
  · have : (c' - 1) * u + u ≤ (c - 1) * u := by
      have := Nat.mul_le_mul_right u (show c' - 1 + 1 ≤ c - 1 by omega)
      rwa [add_mul, one_mul] at this
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega
end Formalism.G0.TopsChoiceProbabilityLemmas
