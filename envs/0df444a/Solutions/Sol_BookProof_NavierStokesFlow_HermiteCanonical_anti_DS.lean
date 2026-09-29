-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.anti_DS
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:12.390362+00:00
-- url     : https://prove2.me/submissions/95b4171f-dcf4-4782-9198-7a3408f580c7

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.anti_DS
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}
set_option autoImplicit false

theorem solution :
    (cre - ann).comp (cre + ann) + (cre + ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp cre - ann.comp ann) := by
  simp only [LinearMap.comp_add, LinearMap.comp_sub, LinearMap.add_comp, LinearMap.sub_comp, two_smul]
  abel

#print axioms solution
