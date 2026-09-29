-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbShort_step
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:04.538776+00:00
-- url     : https://prove2.me/submissions/78aab9d8-a824-4dce-b8e8-ae1fd581f652

import Theorems.Thm_Freiman_middleRepair_equalIIbShort_contacts
import Theorems.Thm_Freiman_middleRepair_equalIIbShort_goodness
import Theorems.Thm_Freiman_middleRepair_row_regular_proper
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middleRepair_equalIIbShort_outer
import Theorems.Thm_Freiman_middle_interval_chain
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbShort → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  intro c t hc hg hr ht
  have hcontact := middleRepair_equalIIbShort_contacts c hc hg hr
  have hgood := middleRepair_equalIIbShort_goodness c hc hg hr
  have hreg := middleRepair_row_regular_proper middleRepair_child_regular c .equalIIbShort hc
  have hout := middleRepair_equalIIbShort_outer c hc hg hr
  have hmem := middle_interval_chain _ _ _ hcontact hout.1 hout.2 ht
  rcases hmem with ⟨d, hd, htd⟩
  exact Or.inr ⟨d, (hreg d hd).1, hgood d hd, (hreg d hd).2, htd⟩
