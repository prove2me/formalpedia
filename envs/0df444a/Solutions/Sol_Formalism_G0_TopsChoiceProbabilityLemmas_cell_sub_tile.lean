-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.cell_sub_tile
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:45.537368+00:00
-- url     : https://prove2.me/submissions/33bfb42e-1f9b-4bbd-a1fb-000e8d63b5d0

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
theorem _root_.solution {r u s c : ℕ} (hc : 1 ≤ c) (hc' : c ≤ 6 * r + 1) :
    cell r u s c ⊆ tile r u s := by
  rw [cell_eq hc]
  unfold tile
  have h1 : (c - 1) * u + u ≤ (6 * r + 1) * u := by
    have := Nat.mul_le_mul_right u (show c - 1 + 1 ≤ 6 * r + 1 by omega)
    rwa [add_mul, one_mul] at this
  have h2 : (s + 1) * ((6 * r + 1) * u) = s * ((6 * r + 1) * u) + (6 * r + 1) * u := by ring
  apply Ico_subset_Ico <;> omega
end Formalism.G0.TopsChoiceProbabilityLemmas
