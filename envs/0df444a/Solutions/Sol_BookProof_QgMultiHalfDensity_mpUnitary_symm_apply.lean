-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.mpUnitary_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:30.283837+00:00
-- url     : https://prove2.me/submissions/ceb60182-97e6-4365-a621-7c74d818cfd1

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.mpUnitary_symm_apply
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_symm_eq
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
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) :
    ((mpUnitary hPhi hPsi hinv).symm h : Y → ℂ) =ᵐ[nu] fun y => (h : X → ℂ) (Psi y) := by

  rw [mpUnitary_symm_eq hPhi hPsi hinv h]
  exact mpIsom_apply hPsi h
