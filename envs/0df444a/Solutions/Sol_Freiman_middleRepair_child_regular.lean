-- Prove2me | solution 1 for Freiman.middleRepair_child_regular
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:24:20.402542+00:00
-- url     : https://prove2.me/submissions/a51456f8-b67b-4e48-8378-2897fcdabf21

import Theorems.Thm_Freiman_middleRepair_child_domain_from_update
import Theorems.Thm_Freiman_middle_parameter_update
import Theorems.Thm_Freiman_middle_parameter_rectangle
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v) := by
  exact middleRepair_child_domain_from_update middle_parameter_update middle_parameter_rectangle
