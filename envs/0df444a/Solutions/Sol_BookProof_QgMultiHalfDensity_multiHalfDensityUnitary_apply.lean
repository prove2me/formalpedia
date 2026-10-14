-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:34.402821+00:00
-- url     : https://prove2.me/submissions/9dd1fee9-5c39-43ad-8a8c-0a6356ee635d

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_apply
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
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
theorem solution
    (g : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod mu)) :
    (multiHalfDensityUnitary mu g : ℝ × X → ℂ)
      =ᵐ[qgSrcMeasure.prod mu] fun p => (g : ℝ × X → ℂ) (p.1 ^ 2, p.2) := mpUnitary_apply _ _ _ g
