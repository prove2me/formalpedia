-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.qgProd_ae_inv_prime
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:27:45.173287+00:00
-- url     : https://prove2.me/submissions/249389d9-032c-44e7-aaa0-636a3035b3fa

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.qgProd_ae_inv'
import Definitions.Def_ChapterNavierStokesFockContinuum
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
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

theorem solution :
    ∀ᵐ p ∂(BookProof.ScalaronDensitized.physMeasure.prod mu),
      qgProdSquare (qgProdSqrt p) = p := by
  have hpos : ∀ᵐ e ∂BookProof.ScalaronDensitized.physMeasure, 0 < e :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hpos] with p hp
  have hsq : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hp.le
  simp [qgProdSqrt, qgProdSquare, qgSquare, Prod.map, hsq]

#print axioms solution

