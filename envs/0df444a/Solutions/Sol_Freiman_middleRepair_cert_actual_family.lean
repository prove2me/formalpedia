-- Prove2me | solution 1 for Freiman.middleRepair_cert_actual_family
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:32.376383+00:00
-- url     : https://prove2.me/submissions/54cec792-dcff-4de5-8487-096c808a0f34

import Theorems.Thm_Freiman_middle_cert_all_families_valid
import Theorems.Thm_Freiman_middleRepair_cert_endpoint_transfer
import Theorems.Thm_Freiman_middleRepair_cert_parameter_domain
import Theorems.Thm_Freiman_middleRepair_cert_row_hypotheses
import Theorems.Thm_Freiman_middleRepair_cert_parent_modes
import Theorems.Thm_Freiman_middleRepair_cert_catalog_sound
import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (f : Fin 11), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val := by
  intro c f hd sp hsp hextra
  have hv := middle_cert_all_families_valid f
  obtain ⟨i,hi,hfamily,hmatch⟩ := hv.1 sp hsp
  have hspec : middleRepairCertSpecHolds c sp := by
    apply middleRepair_cert_endpoint_transfer middleCertData c f (middleCertGoal middleCertData (i+1)) sp hd hfamily hmatch
    intro j hj hmode
    have hp := middleRepair_cert_parameter_domain c hd.1
    apply middleRepair_cert_catalog_sound f i hi hfamily _ _ _ hp.1 hp.2 (middleRepair_cert_parent_modes c f hd) _ j hj hmode
    intro b hb
    have hset := hmatch.2.2.2.2.2.2.2.2.2.2.2
    have hm : b ∈ middleCertFamilyHyp f.val ++ sp.extra := by
      apply List.mem_toFinset.mp
      rw [← hfamily, ← hset]
      exact List.mem_toFinset.mpr hb
    rcases List.mem_append.mp hm with hn | he
    · exact (middleRepair_cert_row_hypotheses c f hd).2 b hn
    · exact hextra b he
  exact hspec hextra
