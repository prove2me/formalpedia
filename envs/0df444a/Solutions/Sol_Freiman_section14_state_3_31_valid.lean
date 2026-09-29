-- Prove2me | solution 1 for Freiman.section14_state_3_31_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:07:33.349982+00:00
-- url     : https://prove2.me/submissions/3681d2d8-c551-40e7-a8ce-cfef52d03cf9

import Theorems.Thm_Freiman_section14_pairWitnesses_all
import Theorems.Thm_Freiman_section14_s0012_metadata
import Theorems.Thm_Freiman_section14_s0012_plans_all
import Theorems.Thm_Freiman_section14_s0012_records_all
import Theorems.Thm_Freiman_section14_s0012_coverage_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : section14StateValid section14Catalog 12 := by
  rcases Freiman.section14_s0012_metadata with ⟨hrect,hr,hs,hparents⟩
  refine ⟨hrect,hr,hs,hparents,Freiman.section14_s0012_plans_all,?_,Freiman.section14_s0012_coverage_all⟩
  intro r hmem hstate
  apply Freiman.section14_s0012_records_all Freiman.section14_pairWitnesses_all r
  exact List.mem_filter.mpr ⟨hmem, by simp [hstate]⟩

#print axioms solution
