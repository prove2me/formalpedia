-- Prove2me | solution 1 for Freiman.middleRepair_good5
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:35.326302+00:00
-- url     : https://prove2.me/submissions/8b0f31ad-cd07-44d2-8638-7938af753549

import Theorems.Thm_Freiman_middle_normalization_domain
import Theorems.Thm_Freiman_middle_gap_fraction
import Theorems.Thm_Freiman_middleRepair_good_gap_bound
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRatio c < (5:ℝ) := by
  intro c hc hg
  have hd := (middle_normalization_domain c hc).1
  have hp := middle_gap_fraction _ hd.1
  have hgap := middleRepair_good_gap_bound c hc hg
  have hL := hd.2.2.1
  have hR := hd.2.2.2
  unfold middleRatio
  apply (div_lt_iff₀ hR).2
  nlinarith
