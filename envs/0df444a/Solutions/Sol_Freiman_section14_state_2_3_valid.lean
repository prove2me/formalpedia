-- Prove2me | solution 1 for Freiman.section14_state_2_3_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T11:43:58.571044+00:00
-- url     : https://prove2.me/submissions/e269ff61-6679-4f92-9ef5-56b3cf9007ec

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_section14_s0007_metadata
import Theorems.Thm_Freiman_section14_s0007_plans_all
import Theorems.Thm_Freiman_section14_s0007_records_all
import Theorems.Thm_Freiman_section14_s0007_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 7 := by
  rcases Freiman.section14_s0007_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.section14_s0007_plans_all,?_,Freiman.section14_s0007_coverage_all⟩
  intro r hmem hstate
  apply Freiman.section14_s0007_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
