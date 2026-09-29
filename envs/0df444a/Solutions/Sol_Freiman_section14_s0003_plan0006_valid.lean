-- Prove2me | solution 1 for Freiman.section14_s0003_plan0006_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T15:24:09.257752+00:00
-- url     : https://prove2.me/submissions/e4b5aabf-70a9-4b04-84e5-8e8e675324c6

import Theorems.Thm_Freiman_section14_s0003_plan0006_metadata
import Theorems.Thm_Freiman_section14_s0003_plan0006_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 3).plans.drop 6).take 1, section14PlanValid section14Catalog (section14State section14Catalog 3) p := by
  have hs : ((section14State section14Catalog 3).plans.drop 6).take 1 = [((section14State section14Catalog 3).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0003_plan0006_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0003_plan0006_specs_all⟩

#print axioms solution
