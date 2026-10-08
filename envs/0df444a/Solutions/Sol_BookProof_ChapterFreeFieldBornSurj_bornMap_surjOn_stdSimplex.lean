-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSurj.bornMap_surjOn_stdSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:51:24.370142+00:00
-- url     : https://prove2.me/submissions/4473d4c8-33e3-4cb1-8029-9f8f4d5df852

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj

open MeasureTheory BookProof.ChapterFreeFieldBornSurj BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn in
theorem solution {n : ℕ} :
    Set.SurjOn (bornMap : EuclideanSpace ℝ (Fin n) → _)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (stdSimplex ℝ (Fin n)) := by
  intro p hp
  have hnn : ∀ k, 0 ≤ p k := hp.1
  have hsum : ∑ k, p k = 1 := hp.2
  refine ⟨bornSection p, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [bornSection, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hnn _), hsum, Real.sqrt_one]
  · funext k
    simp [bornMap, bornSection, Real.sq_sqrt (hnn k)]

