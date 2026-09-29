-- Prove2me | solution 1 for Freiman.section14_s0008_plan0002_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:15:01.474837+00:00
-- url     : https://prove2.me/submissions/d689d9e3-317b-4994-86e2-5244328f071c

import Theorems.Thm_Freiman_section14_s0008_plan0002_metadata
import Theorems.Thm_Freiman_section14_s0008_plan0002_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 8).plans.drop 2).take 1, section14PlanValid section14Catalog (section14State section14Catalog 8) p := by
  have hs : ((section14State section14Catalog 8).plans.drop 2).take 1 = [((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0008_plan0002_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0008_plan0002_specs_all⟩

#print axioms solution
