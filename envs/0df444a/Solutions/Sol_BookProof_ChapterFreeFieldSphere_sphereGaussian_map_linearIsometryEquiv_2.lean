-- Prove2me | solution 2 for BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:26:43.267593+00:00
-- url     : https://prove2.me/submissions/dda97309-31e9-4843-9d1c-10e93c9c77bc

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere

set_option autoImplicit false

open BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldGaussian MeasureTheory in
theorem solution {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (sphereGaussian n).map L = sphereGaussian n := by
  have hstd : (stdGaussian n).map L = stdGaussian n := by
    have h : stdGaussian n = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      ProbabilityTheory.map_pi_eq_stdGaussian
    rw [h]
    exact ProbabilityTheory.stdGaussian_map L
  have hcomm : (⇑L ∘ normalize) = (normalize ∘ ⇑L) := by
    funext x
    simp only [Function.comp_apply, BookProof.ChapterFreeFieldSphere.normalize, map_smul,
      LinearIsometryEquiv.norm_map]
  have hL : Measurable (⇑L) := L.continuous.measurable
  unfold sphereGaussian
  rw [Measure.map_map hL measurable_normalize, hcomm,
    ← Measure.map_map measurable_normalize hL, hstd]
