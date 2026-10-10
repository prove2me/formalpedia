-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:17.475231+00:00
-- url     : https://prove2.me/submissions/97b90e7d-144b-45da-aee5-e73e2aad9ca4

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
import Theorems.Thm_BookProof_NsScalarVectorCurry_eLpNorm_two_sq
open BookProof.NsScalarVectorCurry



open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}
variable [SigmaFinite μ] [SigmaFinite ν]

set_option maxHeartbeats 1000000 in
theorem solution (F : V × W → ℂ) (hF : AEStronglyMeasurable F (μ.prod ν)) :
    ∫⁻ x, (eLpNorm (fun y => F (x, y)) 2 ν) ^ 2 ∂μ = (eLpNorm F 2 (μ.prod ν)) ^ 2 := by

  have hmeas : AEMeasurable (fun z : V × W => ‖F z‖ₑ ^ (2 : ℝ)) (μ.prod ν) :=
    (hF.enorm : AEMeasurable (fun z : V × W => ‖F z‖ₑ) (μ.prod ν)).pow_const _
  calc ∫⁻ x, (eLpNorm (fun y => F (x, y)) 2 ν) ^ 2 ∂μ
      = ∫⁻ x, ∫⁻ y, ‖F (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ := by simp_rw [eLpNorm_two_sq]
    _ = ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) := (lintegral_prod _ hmeas).symm
    _ = (eLpNorm F 2 (μ.prod ν)) ^ 2 := (eLpNorm_two_sq _ _).symm
