-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSectionBij.bornMap_bijOn_nonneg_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:40:31.944891+00:00
-- url     : https://prove2.me/submissions/75f74d15-01bb-4cfa-84e3-bb8b690c92d5

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij

set_option autoImplicit false

open BookProof.ChapterFreeFieldBornSectionBij MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    Set.BijOn (bornMap : EuclideanSpace ℝ (Fin n) → _)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n)
      (stdSimplex ℝ (Fin n)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hs, hx⟩
    rw [mem_sphere_zero_iff_norm] at hs
    refine ⟨fun k => sq_nonneg (x k), ?_⟩
    have h := EuclideanSpace.real_norm_sq_eq x
    rw [hs] at h
    simpa [bornMap] using h.symm
  · rintro x ⟨_, hx⟩ y ⟨_, hy⟩ hxy
    ext k
    have h := congrFun hxy k
    simp only [bornMap] at h
    have hx' : 0 ≤ x k := hx k
    have hy' : 0 ≤ y k := hy k
    nlinarith [sq_nonneg (x k - y k), sq_nonneg (x k + y k)]
  · intro p hp
    obtain ⟨hp0, hp1⟩ := hp
    refine ⟨bornSection p, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      have h := EuclideanSpace.real_norm_sq_eq (bornSection p)
      have h2 : ∑ i, (bornSection p i) ^ 2 = 1 := by
        simp only [bornSection, PiLp.toLp_apply]
        rw [← hp1]
        exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hp0 i)
      rw [h2] at h
      have hn : 0 ≤ ‖bornSection p‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖bornSection p‖ - 1)]
    · intro k
      simp only [bornSection, PiLp.toLp_apply]
      exact Real.sqrt_nonneg _
    · funext k
      simp only [bornMap, bornSection, PiLp.toLp_apply]
      exact Real.sq_sqrt (hp0 k)
