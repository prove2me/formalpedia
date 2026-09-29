-- Prove2me | solution 1 for Freiman.middleRepair_j_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:57.565471+00:00
-- url     : https://prove2.me/submissions/ff431d5f-e0b6-4d1d-bd6b-de302bb3aa9e

import Theorems.Thm_Freiman_middleRepair_j_contact_from_threshold
import Theorems.Thm_Freiman_middle_j_threshold
import Theorems.Thm_Freiman_middle_j_orientation
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k →
      (middleCover (middleRepairJ c k) ∩ middleCover (middleRepairJ c (k+2))).Nonempty := by
  exact middleRepair_j_contact_from_threshold middle_j_threshold middle_j_orientation
