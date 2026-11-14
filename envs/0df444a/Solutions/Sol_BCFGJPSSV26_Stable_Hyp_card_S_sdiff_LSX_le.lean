-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_S_sdiff_LSX_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:08:34.765746+00:00
-- url     : https://prove2.me/submissions/7b7fa16a-56ad-49b7-b85e-790b376f96dc

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
import all Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_S_sdiff_sync_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

end Ctx

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- `|S \ LS_X| ≤ s`. -/
theorem card_S_sdiff_LSX_le {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) :
    (X.S \ X.LSX w₁.OL).card ≤ X.s := by
  classical
  refine (card_le_card ?_).trans H.card_S_sdiff_sync_le
  intro c hc
  rw [mem_sdiff] at hc ⊢
  refine ⟨hc.1, fun h ↦ hc.2 ?_⟩
  obtain ⟨c', hc', rfl⟩ := mem_image.1 h
  refine mem_union_left _ (mem_image.2 ⟨c', mem_union_left _ hc', ?_⟩)
  unfold Ctx.σ₀
  exact if_pos (mem_filter.1 hc').2

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_S_sdiff_LSX_le := @BCFGJPSSV26.Stable.Hyp.card_S_sdiff_LSX_le
