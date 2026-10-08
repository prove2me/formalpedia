-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornCont.stdSimplex_eq_bornMap_image_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:30:13.108144+00:00
-- url     : https://prove2.me/submissions/a00dd233-63f0-4c13-8d62-1ad2ad1b10e8

import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont

set_option autoImplicit false

open MeasureTheory BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    stdSimplex ℝ (Fin n) =
      (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ''
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  ext p
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨(WithLp.toLp 2) (fun k => Real.sqrt (p k)), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
      have : ∑ i, ‖((WithLp.toLp 2) (fun k => Real.sqrt (p k)) : EuclideanSpace ℝ (Fin n)) i‖ ^ 2
          = ∑ i, p i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Real.sq_sqrt (h0 i)]
      rw [this, h1, Real.sqrt_one]
    · funext k
      simp [bornMap, Real.sq_sqrt (h0 k)]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun k => sq_nonneg _, ?_⟩
    rw [mem_sphere_zero_iff_norm] at hx
    have h := EuclideanSpace.norm_sq_eq x
    rw [hx] at h
    simp only [bornMap]
    simpa [Real.norm_eq_abs, sq_abs] using h.symm
