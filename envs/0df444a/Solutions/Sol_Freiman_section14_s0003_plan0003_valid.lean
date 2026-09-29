-- Prove2me | solution 1 for Freiman.section14_s0003_plan0003_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T15:18:10.545954+00:00
-- url     : https://prove2.me/submissions/9a8fee23-a3b5-48e8-b1df-9093b59c9a6f

import Theorems.Thm_Freiman_section14_s0003_plan0003_metadata
import Theorems.Thm_Freiman_section14_s0003_plan0003_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 3).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p := by
  have hs : ((section14State section14Catalog 3).plans.drop 3).take 1 = [((section14State section14Catalog 3).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0003_plan0003_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0003_plan0003_specs_all⟩

#print axioms solution
