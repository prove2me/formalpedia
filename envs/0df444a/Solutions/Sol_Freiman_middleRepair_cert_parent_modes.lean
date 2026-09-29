-- Prove2me | solution 1 for Freiman.middleRepair_cert_parent_modes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:32.445059+00:00
-- url     : https://prove2.me/submissions/b7542bb7-cb58-4528-8e04-456fe5595260

import Theorems.Thm_Freiman_middleRepair_cert_parent_from_criterion
import Theorems.Thm_Freiman_middleRepair_goodness_criterion
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (f : Fin 11), middleRepairCertDomain c f.val → middleRepairCertParentHolds f.val (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) := by
  exact middleRepair_cert_parent_from_criterion middleRepair_goodness_criterion
