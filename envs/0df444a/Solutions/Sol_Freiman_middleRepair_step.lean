-- Prove2me | solution 1 for Freiman.middleRepair_step
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:03.43677+00:00
-- url     : https://prove2.me/submissions/21a4e916-fa50-4cab-a609-04bcff2bdaff

import Theorems.Thm_Freiman_middle_row_exhaustive
import Theorems.Thm_Freiman_middleRepair_mixedA_step
import Theorems.Thm_Freiman_middleRepair_mixedB_step
import Theorems.Thm_Freiman_middleRepair_mixedC_step
import Theorems.Thm_Freiman_middleRepair_equalIShort_step
import Theorems.Thm_Freiman_middleRepair_equalIJ_step
import Theorems.Thm_Freiman_middleRepair_equalIIa_step
import Theorems.Thm_Freiman_middleRepair_equalIIbNormal_step
import Theorems.Thm_Freiman_middleRepair_equalIIbShort_step
import Theorems.Thm_Freiman_middleRepair_equalIIbJ_step
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
      middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d := by
  intro c t hc hg ht
  obtain ⟨r, hr⟩ := middle_row_exhaustive c
  cases r with
  | mixedA => exact middleRepair_mixedA_step c t hc hg hr ht
  | mixedB => exact middleRepair_mixedB_step c t hc hg hr ht
  | mixedC => exact middleRepair_mixedC_step c t hc hg hr ht
  | equalIShort => exact middleRepair_equalIShort_step c t hc hg hr ht
  | equalIJ => exact middleRepair_equalIJ_step c t hc hg hr ht
  | equalIIa => exact middleRepair_equalIIa_step c t hc hg hr ht
  | equalIIbNormal => exact middleRepair_equalIIbNormal_step c t hc hg hr ht
  | equalIIbShort => exact middleRepair_equalIIbShort_step c t hc hg hr ht
  | equalIIbJ => exact middleRepair_equalIIbJ_step c t hc hg hr ht
