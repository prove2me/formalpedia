-- Prove2me | solution 1 for Freiman.section14_state_2_2_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:59:55.699367+00:00
-- url     : https://prove2.me/submissions/df2ba3fa-01b8-4468-9913-557b82382885

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_workReverse20260919_s0006_metadata
import Theorems.Thm_Freiman_workReverse20260919_s0006_plans_all
import Theorems.Thm_Freiman_workReverse20260919_s0006_records_all
import Theorems.Thm_Freiman_workReverse20260919_s0006_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 6 := by
  rcases Freiman.workReverse20260919_s0006_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.workReverse20260919_s0006_plans_all,?_,Freiman.workReverse20260919_s0006_coverage_all⟩
  intro r hmem hstate
  apply Freiman.workReverse20260919_s0006_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
