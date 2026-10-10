-- Prove2me | solution 1 for BookProof.MixedLinearEsa.contDiff_polyPhase
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:03:37.57198+00:00
-- url     : https://prove2.me/submissions/2b4d5b92-ac08-4205-9e81-1d59443c866a

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.contDiff_polyPhase
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem solution (c : ℕ → ℝ) (n : ℕ) (m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyPhase c n m) := by

  unfold polyPhase
  refine ContDiff.sum fun i _ => ?_
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V => (inner ℝ x m : ℝ)) :=
    ((innerSL ℝ).flip m).contDiff
  exact (((contDiff_const.mul (h.pow (i + 1))).div_const _)).neg
