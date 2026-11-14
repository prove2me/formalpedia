-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_O1_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:06:52.795857+00:00
-- url     : https://prove2.me/submissions/f81b7fea-8d49-4e83-8b23-e2180f3b60d7

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

/-- `|O₁| ≤ s`. -/
theorem card_O1_le : X.O1.card ≤ X.s := by
  classical
  refine (card_le_card fun c hc ↦ ?_).trans H.card_unsynced_le_s
  simp only [Ctx.O1, Ctx.OS0, Ctx.Osync, mem_sdiff, mem_union, mem_filter, not_or] at hc ⊢
  exact ⟨hc.1, fun h ↦ hc.2.1 ⟨hc.1, h⟩⟩

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_O1_le := @BCFGJPSSV26.Stable.Hyp.card_O1_le
