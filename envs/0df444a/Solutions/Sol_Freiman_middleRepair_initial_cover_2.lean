-- Prove2me | solution 2 for Freiman.middleRepair_initial_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:04:13.646896+00:00
-- url     : https://prove2.me/submissions/03ba6154-007e-4360-8bd9-13bc54cb5f98

import Definitions.Def_Freiman_middleRepair
import Theorems.Thm_Freiman_middle_initial_certificates
import Theorems.Thm_Freiman_middle_initial_contacts_lower
import Theorems.Thm_Freiman_middle_initial_contacts_upper
import Theorems.Thm_Freiman_middle_initial_endpoint_edges
import Theorems.Thm_Freiman_middle_initial_chain_assembly
import Theorems.Thm_Freiman_middle_interval_chain
import Theorems.Thm_Freiman_middleRepair_good38

open Freiman

-- The 15 explicit `middleRoot`s already cover `[sqrt 21, 128/25]` (Proved chain
-- assembly over the Proved root certificates and contacts), and each root is
-- regular by its certificate. The only remaining ingredient is goodness of the 15
-- roots, which is exactly the general criterion `middleRepair_good38` applied to the
-- certificate's ratio bound `middleRatio (middleRoot i) < 19/5`.
theorem solution :
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ),
      ∃ i : Fin 15, middleRegular (middleRoot i) ∧ middleRepairGood (middleRoot i) ∧
        t∈middleCover (middleRoot i) := by
  intro t ht
  obtain ⟨i, hcover⟩ :=
    middle_initial_chain_assembly middle_initial_certificates
      (fun i hi => middle_initial_contacts_lower middle_initial_certificates i hi)
      (fun i hlo hi => middle_initial_contacts_upper middle_initial_certificates i hlo hi)
      (middle_initial_endpoint_edges middle_initial_certificates).1
      (middle_initial_endpoint_edges middle_initial_certificates).2
      middle_interval_chain t ht
  exact ⟨i, (middle_initial_certificates i).1,
    middleRepair_good38 (middleRoot i) (middle_initial_certificates i).1
      (middle_initial_certificates i).2.1,
    hcover⟩
