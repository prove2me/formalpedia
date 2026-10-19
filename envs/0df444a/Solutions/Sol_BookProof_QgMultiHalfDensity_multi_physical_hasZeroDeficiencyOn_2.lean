-- Prove2me | solution 2 for BookProof.QgMultiHalfDensity.multi_physical_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:45:46.873245+00:00
-- url     : https://prove2.me/submissions/e8bb1e1a-3c40-41ca-a197-d34e4bc85afa

import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_hasZeroDeficiencyOn
-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.multi_physical_hasZeroDeficiencyOn
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity
open BookProof.ScalaronDensitized
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


theorem solution {V : ℝ × X → ℝ} (hV : Measurable V) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (BookProof.ScalaronDensitized.physMeasure.prod mu) V)
      (multOp (BookProof.ScalaronDensitized.physMeasure.prod mu) hV) := by
  exact BookProof.NavierStokesFlow.FockContinuum.multOp_hasZeroDeficiencyOn _ hV

