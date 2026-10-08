-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSurj.bornSection_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:54:10.54803+00:00
-- url     : https://prove2.me/submissions/91d0d4ed-9668-4144-826c-c7d152efd44a

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj

set_option autoImplicit false

open BookProof.ChapterFreeFieldBornSurj MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn in
theorem solution {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    bornSection p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
  have h : ∑ i, ‖(bornSection p) i‖ ^ 2 = 1 := by
    rw [← hp.2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bornSection, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (hp.1 i)
  rw [h, Real.sqrt_one]
