-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:51:55.731954+00:00
-- url     : https://prove2.me/submissions/220fd73d-b97c-49b2-8369-d90bc7c80152

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj

set_option autoImplicit false

open BookProof.ChapterFreeFieldBornSurj MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn in
theorem solution {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    bornMap (bornSection p) = p := by
  funext k
  simp only [bornMap, bornSection]
  exact Real.sq_sqrt (hp.1 k)

#print axioms solution
