-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.cell_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:32.808347+00:00
-- url     : https://prove2.me/submissions/7cc05a5f-9ea7-4a11-a899-e010c1f41b3d

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
theorem _root_.solution {r u s c : ℕ} (hc : 1 ≤ c) :
    cell r u s c = Ico (s * ((6 * r + 1) * u) + (c - 1) * u)
      (s * ((6 * r + 1) * u) + (c - 1) * u + u) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  unfold cell
  simp only [Nat.add_sub_cancel]
  congr 1
  ring
end Formalism.G0.TopsChoiceProbabilityLemmas
