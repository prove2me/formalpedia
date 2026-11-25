-- Prove2me | solution 1 for Formalism.RankGapBounds.FormsTensorLocalization.functoriality_reduction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:57.919658+00:00
-- url     : https://prove2.me/submissions/3acfeffa-15c9-4a66-bec7-200a64271dfc

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.FormsTensorLocalization
open Formalism.UG
namespace Formalism.RankGapBounds.FormsTensorLocalization
theorem _root_.solution : FunctStep := by
  intro G _ Γ K k _ W _ _ ρK U V l e hVU f hf
  obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hf1, ?_⟩
  rw [Submodule.mem_pi] at hf2 ⊢
  intro g _
  exact hVU _ (hf2 g (Set.mem_univ g))
end Formalism.RankGapBounds.FormsTensorLocalization
