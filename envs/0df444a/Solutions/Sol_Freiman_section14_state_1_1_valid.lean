-- Prove2me | solution 1 for Freiman.section14_state_1_1_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:57:44.133057+00:00
-- url     : https://prove2.me/submissions/0a41aa88-3758-427d-86cb-a8d51c699cf7

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_workReverse20260919_s0001_metadata
import Theorems.Thm_Freiman_workReverse20260919_s0001_plans_all
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_all
import Theorems.Thm_Freiman_workReverse20260919_s0001_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 1 := by
  rcases Freiman.workReverse20260919_s0001_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.workReverse20260919_s0001_plans_all,?_,Freiman.workReverse20260919_s0001_coverage_all⟩
  intro r hmem hstate
  apply Freiman.workReverse20260919_s0001_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
