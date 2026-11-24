-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.subTopBot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:08.648603+00:00
-- url     : https://prove2.me/submissions/69a596be-0f83-4746-9c60-d53ced202fa3

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open FilPhi
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : SubTopBot := by
  intro LL _ D _ _ n Emb _ F
  constructor
  · refine ⟨fun x _ => Submodule.mem_top, ?_⟩
    simp only [top_inf_eq]
    exact F.internal.submodule_iSup_eq_top.symm
  · refine ⟨fun x hx => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    · simp
end Formalism.WeaklyAdmissibleFiltrations
