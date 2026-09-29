-- Prove2me | solution 1 for Freiman.section14_s0014_plan0001_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:07:18.089636+00:00
-- url     : https://prove2.me/submissions/6af53d48-de15-4b1d-94a2-39ebc909f824

import Theorems.Thm_Freiman_section14_s0014_plan0001_metadata
import Theorems.Thm_Freiman_section14_s0014_plan0001_specs_all
import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 14).plans.drop 1).take 1, section14PlanValid section14Catalog (section14State section14Catalog 14) p := by
  have hs : ((section14State section14Catalog 14).plans.drop 1).take 1 = [((section14State section14Catalog 14).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.section14_s0014_plan0001_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.section14_s0014_plan0001_specs_all⟩

#print axioms solution
