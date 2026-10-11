-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:24:55.918988+00:00
-- url     : https://prove2.me/submissions/a05c2ef8-1cb6-4f50-bc7d-f2dd41c4e08d

-- Generated from ChapterNavierStokesFockContinuum.lean — solution of BookProof.NavierStokesFlow.FockContinuum.mem_boundedEnergyCore
import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum



open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution {μ : Measure X} {g : X → ℝ} {f : Lp ℂ 2 μ} :
    f ∈ boundedEnergyCore μ g ↔ ∃ n : ℕ, ∀ᵐ x ∂μ, ¬ (|g x| ≤ (n : ℝ)) → (f : X → ℂ) x = 0 := Iff.rfl
