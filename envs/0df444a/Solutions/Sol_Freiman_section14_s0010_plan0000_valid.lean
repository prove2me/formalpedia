-- Prove2me | solution 1 for Freiman.section14_s0010_plan0000_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T18:15:44.538562+00:00
-- url     : https://prove2.me/submissions/c970e2a5-0827-44b4-81e1-8d8792713bdb

import Theorems.Thm_Freiman_section14_s0010_plan0000_metadata
import Theorems.Thm_Freiman_section14_s0010_plan0000_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 10).plans.drop 0).take 1, section14PlanValid section14Catalog (section14State section14Catalog 10) p := by
  have hs : ((section14State section14Catalog 10).plans.drop 0).take 1 = [((section14State section14Catalog 10).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0010_plan0000_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0010_plan0000_specs_all⟩

#print axioms solution
