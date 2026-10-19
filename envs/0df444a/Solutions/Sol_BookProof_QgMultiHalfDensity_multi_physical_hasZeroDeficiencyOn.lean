-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.multi_physical_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:44:57.792086+00:00
-- url     : https://prove2.me/submissions/b3210046-feb9-41c5-83ff-2c0051ad5fcf

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.multi_physical_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Theorems.Thm_BookProof_QgMultiHalfDensity_multi_hasZeroDeficiencyOn_transfer
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_hasZeroDeficiencyOn
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
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
theorem solution {V : ℝ × X → ℝ} (hV : Measurable V) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (BookProof.ScalaronDensitized.physMeasure.prod mu) V)
      (multOp (BookProof.ScalaronDensitized.physMeasure.prod mu) hV) := multi_hasZeroDeficiencyOn_transfer mu hV (multOp_hasZeroDeficiencyOn _ _)
