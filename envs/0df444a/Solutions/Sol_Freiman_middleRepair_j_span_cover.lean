-- Prove2me | solution 1 for Freiman.middleRepair_j_span_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:19:56.285778+00:00
-- url     : https://prove2.me/submissions/6cb50890-d64c-4475-a1eb-1c1b73d1af87

import Theorems.Thm_Freiman_middleRepair_j_chain_limit_cover
import Theorems.Thm_Freiman_middleRepair_j_contacts
import Theorems.Thm_Freiman_middleRepair_j_endpoint_limit
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (r : MiddleRow), middleRegular c → middleRowCondition c r → middleEssentialJ r = true →
      ∀ t ∈ middleRepairJSpan c, t=middleLimitValue c ∨ ∃ k : ℕ, 1 ≤ k ∧ t∈middleCover (middleRepairJ c k) := by
  intro c r hc hr hj
  exact middleRepair_j_chain_limit_cover c (fun k hk => middleRepair_j_contacts c r k hc hr hj hk)
    (middleRepair_j_endpoint_limit c).1 (middleRepair_j_endpoint_limit c).2
