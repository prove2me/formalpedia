-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.sq_diff
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:10.827745+00:00
-- url     : https://prove2.me/submissions/a73d99d6-2fd5-429d-a786-e563effe3ead

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.sq_diff
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}
set_option autoImplicit false

theorem solution :
    (cre + ann).comp (cre + ann) - (cre - ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp ann + ann.comp cre) := by
  simp only [LinearMap.comp_add, LinearMap.comp_sub, LinearMap.add_comp, LinearMap.sub_comp, two_smul]
  abel

#print axioms solution
