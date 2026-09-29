-- Prove2me | solution 1 for Freiman.middleRepair_equalIJ_step
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:04.929838+00:00
-- url     : https://prove2.me/submissions/1fe7ad7a-e221-4fd7-99e4-92d9bcc613e7

import Theorems.Thm_Freiman_middleRepair_equalIJ_contacts
import Theorems.Thm_Freiman_middleRepair_equalIJ_goodness
import Theorems.Thm_Freiman_middleRepair_row_regular_proper
import Theorems.Thm_Freiman_middleRepair_child_regular
import Theorems.Thm_Freiman_middleRepair_equalIJ_anchors
import Theorems.Thm_Freiman_middleRepair_j_splice
import Theorems.Thm_Freiman_middle_endpoint_order
import Theorems.Thm_Freiman_middleRepair_j_regular_proper
import Theorems.Thm_Freiman_middleRepair_j_span_cover
import Theorems.Thm_Freiman_middle_limit_realized
import Theorems.Thm_Freiman_middleRepair_j_good
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → middleRowCondition c .equalIJ → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  intro c t hc hg hr ht
  have hcontact := middleRepair_equalIJ_contacts c hc hg hr
  have hgood := middleRepair_equalIJ_goodness c hc hg hr
  have hreg := middleRepair_row_regular_proper middleRepair_child_regular c .equalIJ hc
  have hanchor := middleRepair_equalIJ_anchors c hc hg hr
  have hj1reg := (middleRepair_j_regular_proper middleRepair_child_regular c 1 hc (by omega)).1
  have hne : (middleCover (middleRepairJ c 1)).Nonempty := ⟨_, le_rfl, middle_endpoint_order _ hj1reg⟩
  have hsplit := middleRepair_j_splice c _ hcontact hanchor hne ht
  rcases hsplit with hmem | hjspan
  · rcases hmem with ⟨d, hd, htd⟩
    exact Or.inr ⟨d, (hreg d hd).1, hgood d hd, (hreg d hd).2, htd⟩
  · rcases middleRepair_j_span_cover c .equalIJ hc hr rfl t hjspan with heq | ⟨k,hk,hkt⟩
    · subst t
      exact Or.inl (middle_limit_realized c)
    · have hkr := middleRepair_j_regular_proper middleRepair_child_regular c k hc hk
      exact Or.inr ⟨middleRepairJ c k, hkr.1, middleRepair_j_good c .equalIJ k hc hr rfl hk, hkr.2, hkt⟩
