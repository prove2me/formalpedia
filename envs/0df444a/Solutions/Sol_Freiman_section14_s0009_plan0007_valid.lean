-- Prove2me | solution 1 for Freiman.section14_s0009_plan0007_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T22:36:45.400544+00:00
-- url     : https://prove2.me/submissions/36552866-3b50-423a-96d7-f2972299cfe0

import Theorems.Thm_Freiman_section14_s0009_plan0007_metadata
import Theorems.Thm_Freiman_section14_s0009_plan0007_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 9).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 9) p := by
  have hs : ((section14State section14Catalog 9).plans.drop 7).take 1 = [((section14State section14Catalog 9).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0009_plan0007_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0009_plan0007_specs_all⟩

#print axioms solution
