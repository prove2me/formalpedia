-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:06:53.943204+00:00
-- url     : https://prove2.me/submissions/40856b6c-228a-4814-a127-b1384580d7d8

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
import all Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_unsynced_lt

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace FewNotInSync

variable (X : Ctx)

end FewNotInSync

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

open FewNotInSync

open Classical in
theorem card_unsynced_le_s : (X.O.filter fun c ↦ ¬ X.IsSynced c).card ≤ X.s := by
  have h := H.card_unsynced_lt.le.trans H.s_ge
  exact_mod_cast h

/-- `|S \ σ_sync(O_sync)| ≤ s`: the partners are distinct, and `|S| = |O|`. -/
theorem card_S_sdiff_sync_le : (X.S \ X.Osync.image X.σsync).card ≤ X.s := by
  classical
  have himg : X.Osync.image X.σsync ⊆ X.S := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
    exact (H.σsync_spec (mem_filter.1 hc').2).1
  have hcard : (X.Osync.image X.σsync).card = X.Osync.card := card_image_of_injOn H.σsync_injOn
  have hO : X.O.card = X.S.card := by rw [H.isOpt.card, H.alo.1]
  have hsplit : X.Osync.card + (X.O.filter fun c ↦ ¬ X.IsSynced c).card = X.O.card :=
    card_filter_add_card_filter_not _
  rw [card_sdiff_of_subset himg, hcard]
  have := H.card_unsynced_le_s
  omega

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le := @BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le
