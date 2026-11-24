-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.tile_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:21.038853+00:00
-- url     : https://prove2.me/submissions/0b1d47f8-4a2e-4c77-870f-ccaca287ac4a

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
theorem _root_.solution {r u s x : ℕ} (h : x ∈ tile r u s) : x / ((6 * r + 1) * u) = s := by
  unfold tile at h
  rw [mem_Ico] at h
  exact Nat.div_eq_of_lt_le h.1 h.2
end Formalism.G0.TopsChoiceProbabilityLemmas
