-- Prove2me | solution 1 for Freiman.middleRepair_initial_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:17.349181+00:00
-- url     : https://prove2.me/submissions/0a0bd7ac-0bf3-4e52-a7a5-7dc2373c2091

import Theorems.Thm_Freiman_middle_initial_certificates
import Theorems.Thm_Freiman_middle_initial_contacts_lower
import Theorems.Thm_Freiman_middle_initial_contacts_upper
import Theorems.Thm_Freiman_middle_initial_endpoint_edges
import Theorems.Thm_Freiman_middle_initial_chain_assembly
import Theorems.Thm_Freiman_middle_interval_chain
import Theorems.Thm_Freiman_middleRepair_good38
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ), ∃ i : Fin 15, middleRegular (middleRoot i) ∧ middleRepairGood (middleRoot i) ∧ t∈middleCover (middleRoot i) := by
  intro t ht
  have hc := middle_initial_certificates
  have hedges := middle_initial_endpoint_edges hc
  obtain ⟨i,hi⟩ := middle_initial_chain_assembly hc (middle_initial_contacts_lower hc)
    (middle_initial_contacts_upper hc) hedges.1 hedges.2 middle_interval_chain t ht
  exact ⟨i,(hc i).1,middleRepair_good38 _ (hc i).1 (hc i).2.1,hi⟩
