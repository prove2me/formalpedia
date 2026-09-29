-- Prove2me | solution 1 for Freiman.section14_state_2_1_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:48:33.244536+00:00
-- url     : https://prove2.me/submissions/a0898710-eca1-4c74-b4e9-39c63e5f4129

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_metadata
import Theorems.Thm_Freiman_workReverse20260919_s0005_plans_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 5 := by
  rcases Freiman.workReverse20260919_s0005_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.workReverse20260919_s0005_plans_all,?_,Freiman.workReverse20260919_s0005_coverage_all⟩
  intro r hmem hstate
  apply Freiman.workReverse20260919_s0005_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
