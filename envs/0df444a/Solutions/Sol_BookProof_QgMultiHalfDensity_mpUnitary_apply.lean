-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.mpUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:29.099997+00:00
-- url     : https://prove2.me/submissions/65033276-5ff6-448f-8804-6cb358a7f752

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.mpUnitary_apply
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QgMultiHalfDensity




open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}

set_option maxHeartbeats 1000000 in
theorem solution (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (g : Lp ℂ 2 nu) :
    (mpUnitary hPhi hPsi hinv g : X → ℂ) =ᵐ[mu] fun x => (g : Y → ℂ) (Phi x) := mpIsom_apply hPhi g
