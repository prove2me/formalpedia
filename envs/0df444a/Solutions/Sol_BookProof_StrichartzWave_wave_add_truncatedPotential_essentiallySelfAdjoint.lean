-- Prove2me | solution 1 for BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:28:12.147098+00:00
-- url     : https://prove2.me/submissions/4c476a2e-aa70-4990-a62e-65cdd13e585a

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_memLp_top_of_continuous_of_hasCompactSupport
import Theorems.Thm_BookProof_StrichartzWave_wave_add_boundedPotentialOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_StrichartzWave_exists_smooth_cutoff
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : Function.HasTemperateGrowth W) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = W x) ∧ (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) := by

  obtain ⟨χ, hχsmooth, hχc, hχone, -, hχzero, -⟩ := exists_smooth_cutoff (V := SpaceTime n) R
  have hWcont : Continuous W := hW.1.continuous
  have hcs : HasCompactSupport (fun x => W x * χ x) := hχc.mul_left
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => W x * χ x) := hW.1.mul hχsmooth
  refine ⟨fun x => W x * χ x, hcs.hasTemperateGrowth hsmooth, ?_, ?_, ?_⟩
  · intro x hx
    change W x * χ x = W x
    rw [hχone x hx, mul_one]
  · intro x hx
    change W x * χ x = 0
    rw [hχzero x hx, mul_zero]
  · refine wave_add_boundedPotentialOp_essentiallySelfAdjoint n _ (hcs.hasTemperateGrowth hsmooth)
      (memLp_top_of_continuous_of_hasCompactSupport (hWcont.mul hχsmooth.continuous) hcs)
