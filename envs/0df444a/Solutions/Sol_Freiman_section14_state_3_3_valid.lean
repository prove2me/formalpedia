-- Prove2me | solution 1 for Freiman.section14_state_3_3_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:10:08.260844+00:00
-- url     : https://prove2.me/submissions/7b986002-63f8-4a88-9069-c077d943176a

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_section14_s0011_metadata
import Theorems.Thm_Freiman_section14_s0011_plans_all
import Theorems.Thm_Freiman_section14_s0011_records_all
import Theorems.Thm_Freiman_section14_s0011_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 11 := by
  rcases Freiman.section14_s0011_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.section14_s0011_plans_all,?_,Freiman.section14_s0011_coverage_all⟩
  intro r hmem hstate
  apply Freiman.section14_s0011_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
