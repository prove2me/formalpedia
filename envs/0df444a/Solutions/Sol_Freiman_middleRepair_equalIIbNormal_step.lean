-- Prove2me | solution 1 for Freiman.middleRepair_equalIIbNormal_step
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:02.230397+00:00
-- url     : https://prove2.me/submissions/445fe41c-47a0-410e-baa0-e3f512fcc3f9

import Theorems.Thm_Freiman_middleRepair_equalIIbNormal_contacts
import Theorems.Thm_Freiman_middleRepair_equalIIbNormal_goodness
import Theorems.Thm_Freiman_middleRepair_row_regular_proper
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middleRepair_equalIIbNormal_outer
import Theorems.Thm_Freiman_middle_interval_chain
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbNormal → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  intro c t hc hg hr ht
  have hcontact := middleRepair_equalIIbNormal_contacts c hc hg hr
  have hgood := middleRepair_equalIIbNormal_goodness c hc hg hr
  have hreg := middleRepair_row_regular_proper middleRepair_child_regular c .equalIIbNormal hc
  have hout := middleRepair_equalIIbNormal_outer c hc hg hr
  have hmem := middle_interval_chain _ _ _ hcontact hout.1 hout.2 ht
  rcases hmem with ⟨d, hd, htd⟩
  exact Or.inr ⟨d, (hreg d hd).1, hgood d hd, (hreg d hd).2, htd⟩
