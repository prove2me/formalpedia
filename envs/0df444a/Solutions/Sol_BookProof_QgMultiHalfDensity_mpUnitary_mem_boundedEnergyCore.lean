-- Prove2me | solution 1 for BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:31.742508+00:00
-- url     : https://prove2.me/submissions/8c7831ba-4e06-4c7d-a914-09ce6aae8388

-- Generated from ChapterQgMultiHalfDensity.lean — solution of BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_apply
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesFockContinuum
open BookProof.QgMultiHalfDensity




open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x)
    (x : boundedEnergyCore nu g) :
    mpUnitary hPhi hPsi hinv (x : Lp ℂ 2 nu) ∈ boundedEnergyCore mu (fun t => g (Phi t)) := by

  obtain ⟨n, hn⟩ := x.2
  refine ⟨n, ?_⟩
  filter_upwards [mpUnitary_apply hPhi hPsi hinv (x : Lp ℂ 2 nu),
    hPhi.quasiMeasurePreserving.ae hn] with t ht hpt hbig
  rw [ht]
  exact hpt hbig
