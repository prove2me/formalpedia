-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:56:35.364916+00:00
-- url     : https://prove2.me/submissions/87145838-0344-404e-a3ff-459f9bf3bfcf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_hasZeroDeficiencyOn_transfer
import Theorems.Thm_BookProof_QgMultiHalfDensity_qgProd_ae_inv_prime
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
theorem solution {V : ℝ × X → ℝ} (hV : Measurable V)
    (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (qgSrcMeasure.prod mu) fun p => V (qgProdSquare p))
      (multOp (qgSrcMeasure.prod mu) (hV.comp (measurePreserving_qgProdSquare mu).measurable))) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (BookProof.ScalaronDensitized.physMeasure.prod mu) V)
      (multOp (BookProof.ScalaronDensitized.physMeasure.prod mu) hV) :=
  mpUnitary_hasZeroDeficiencyOn_transfer (measurePreserving_qgProdSquare mu)
      (measurePreserving_qgProdSqrt mu) (qgProd_ae_inv mu) (qgProd_ae_inv_prime mu) hV hflat
