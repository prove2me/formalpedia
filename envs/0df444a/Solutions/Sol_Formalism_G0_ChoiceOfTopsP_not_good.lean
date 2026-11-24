-- Prove2me | solution 1 for Formalism.G0.ChoiceOfTopsP.not_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:21.902083+00:00
-- url     : https://prove2.me/submissions/16b93694-67fc-490a-bc45-a846ed68e8b2

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.ChoiceOfTopsP
namespace Formalism.G0.ChoiceOfTopsP
theorem _root_.solution {n : ℕ} {T : Finset ℕ} {L₂ K r N₁ G : ℕ} (h : ¬ GoodOrbit n T L₂ K r N₁ G) :
    ¬ CondA n T L₂ K ∨ (¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ∨ ¬ CondC n T G ∨ T.card < N₁ := by
  unfold GoodOrbit at h
  by_cases hN : N₁ ≤ T.card
  · tauto
  · right; right; right; omega
end Formalism.G0.ChoiceOfTopsP
