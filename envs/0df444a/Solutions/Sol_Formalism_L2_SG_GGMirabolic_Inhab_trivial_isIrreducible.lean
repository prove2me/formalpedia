-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.trivial_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:12.263872+00:00
-- url     : https://prove2.me/submissions/7c0f1418-dfd6-42a7-bf49-bf286d7bf9c4

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution (G : Type) [Group G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h2 := congrArg (fun W : Subrepresentation (Representation.trivial ℂ G ℂ) => W.toSubmodule) h
    exact (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) h2
  · rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
    · left; apply Subrepresentation.toSubmodule_injective; rw [h]; rfl
    · right; apply Subrepresentation.toSubmodule_injective; rw [h]; rfl
end Formalism.L2.SG.GGMirabolic.Inhab
