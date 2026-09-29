-- Prove2me | solution 1 for Freiman.section14_state_31_3_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T21:52:59.410345+00:00
-- url     : https://prove2.me/submissions/c3db0039-cfa8-44e2-9ac7-9da0d7999bbe

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_section14_s0015_metadata
import Theorems.Thm_Freiman_section14_s0015_plans_all
import Theorems.Thm_Freiman_section14_s0015_records_all
import Theorems.Thm_Freiman_section14_s0015_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 15 := by
  rcases Freiman.section14_s0015_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.section14_s0015_plans_all,?_,Freiman.section14_s0015_coverage_all⟩
  intro r hmem hstate
  apply Freiman.section14_s0015_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
