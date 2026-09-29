-- Prove2me | solution 1 for Freiman.section14_state_31_1_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T10:20:45.983261+00:00
-- url     : https://prove2.me/submissions/18c73ac2-76c4-4226-9844-8f727824d811

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_workReverse20260919_s0013_metadata
import Theorems.Thm_Freiman_workReverse20260919_s0013_plans_all
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_all
import Theorems.Thm_Freiman_workReverse20260919_s0013_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 13 := by
  rcases Freiman.workReverse20260919_s0013_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.workReverse20260919_s0013_plans_all,?_,Freiman.workReverse20260919_s0013_coverage_all⟩
  intro r hmem hstate
  apply Freiman.workReverse20260919_s0013_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
