-- Prove2me | solution 2 for BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:45:57.091098+00:00
-- url     : https://prove2.me/submissions/44eaf8ca-7b3e-4033-904f-5b202ddf9ec3

import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_hasZeroDeficiencyOn
-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
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


theorem solution {V : ℝ × X → ℝ} (hV : Measurable V)
    (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (qgSrcMeasure.prod mu) fun p => V (qgProdSquare p))
      (multOp (qgSrcMeasure.prod mu) (hV.comp (measurePreserving_qgProdSquare mu).measurable))) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (BookProof.ScalaronDensitized.physMeasure.prod mu) V)
      (multOp (BookProof.ScalaronDensitized.physMeasure.prod mu) hV) := by
  exact BookProof.NavierStokesFlow.FockContinuum.multOp_hasZeroDeficiencyOn _ hV

