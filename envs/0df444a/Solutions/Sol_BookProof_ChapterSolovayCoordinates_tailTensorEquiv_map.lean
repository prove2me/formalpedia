-- Prove2me | solution 1 for BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T15:54:17.725926+00:00
-- url     : https://prove2.me/submissions/31eea1b9-54d3-43ff-b5f9-96f1f7c47c7d

-- Generated from ChapterSolovayCoordinates.lean — solution of BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates



open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    Measure.map tailTensorEquiv
      (coordinateTailMeasure.prod coordinateTailMeasure) = coordinateTailMeasure := by

  let e1 : CoordinateTail × CoordinateTail ≃ᵐ (Fin 2 → CoordinateTail) :=
    MeasurableEquiv.finTwoArrow.symm
  let e2 : (Fin 2 → CoordinateTail) ≃ᵐ (Fin 2 × ℕ → ℝ) :=
    (MeasurableEquiv.curry (Fin 2) ℕ ℝ).symm
  let e3 : (Fin 2 × ℕ → ℝ) ≃ᵐ CoordinateTail :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) pairIndexEquiv
  change Measure.map (e3 ∘ (e2 ∘ e1))
    (coordinateTailMeasure.prod coordinateTailMeasure) = coordinateTailMeasure
  rw [← Measure.map_map e3.measurable (e2.measurable.comp e1.measurable)]
  rw [← Measure.map_map e2.measurable e1.measurable]
  have h1 : Measure.map e1
      (coordinateTailMeasure.prod coordinateTailMeasure) =
      Measure.pi (fun _ : Fin 2 => coordinateTailMeasure) := by
    exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e1).2
      (measurePreserving_finTwoArrow coordinateTailMeasure).map_eq.symm
  rw [h1, ← Measure.infinitePi_eq_pi]
  change Measure.map e3
    (Measure.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ).symm
      (Measure.infinitePi fun _ : Fin 2 => coordinateTailMeasure)) =
    coordinateTailMeasure
  change Measure.map e3
    (Measure.map (MeasurableEquiv.curry (Fin 2) ℕ ℝ).symm
      (Measure.infinitePi fun _ : Fin 2 =>
        Measure.infinitePi fun _ : ℕ => standardGaussian)) =
    Measure.infinitePi fun _ : ℕ => standardGaussian
  rw [Measure.infinitePi_map_curry_symm]
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : ℕ => standardGaussian) pairIndexEquiv
