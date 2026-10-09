-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:56:36.758311+00:00
-- url     : https://prove2.me/submissions/c4453c1b-0637-41ac-aba4-9a42b5d2a8c0

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
open BookProof.QgMultiHalfDensity




open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable [SFinite mu]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    ∃ _W : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod
        (volume : Measure (Fin n → ℝ)))
      ≃ₗᵢ[ℂ] Lp ℂ 2 (qgSrcMeasure.prod (volume : Measure (Fin n → ℝ))), True := ⟨fieldHalfDensityUnitary n, trivial⟩
