-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:36:07.749491+00:00
-- url     : https://prove2.me/submissions/f0963cdd-70c0-4f0a-bc35-a3cca3fd173f

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Mathlib
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_hasZeroDeficiencyOn
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QgMultiHalfDensity



open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}
open BookProof.QgMultiHalfDensity in
theorem solution (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x)
    (hinv' : ∀ᵐ y ∂nu, Phi (Psi y) = y) (hg : Measurable g)
    (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore mu (fun t => g (Phi t))) (multOp mu (hg.comp hPhi.measurable))) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore nu g) (multOp nu hg) := by 
  exact BookProof.NavierStokesFlow.FockContinuum.multOp_hasZeroDeficiencyOn nu hg
