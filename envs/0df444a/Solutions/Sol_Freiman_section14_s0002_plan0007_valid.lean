-- Prove2me | solution 1 for Freiman.section14_s0002_plan0007_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:42:03.11061+00:00
-- url     : https://prove2.me/submissions/b8f0100a-5392-4ae3-b100-b34b3f9c59a2

import Theorems.Thm_Freiman_section14_s0002_plan0007_metadata
import Theorems.Thm_Freiman_section14_s0002_plan0007_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 2).plans.drop 7).take 1, section14PlanValid section14Catalog (section14State section14Catalog 2) p := by
  have hs : ((section14State section14Catalog 2).plans.drop 7).take 1 = [((section14State section14Catalog 2).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0002_plan0007_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0002_plan0007_specs_all⟩

#print axioms solution
