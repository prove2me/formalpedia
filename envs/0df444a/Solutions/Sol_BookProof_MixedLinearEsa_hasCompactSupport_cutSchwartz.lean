-- Prove2me | solution 1 for BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:59:36.988031+00:00
-- url     : https://prove2.me/submissions/d88ea5b1-2a69-4247-a0e2-5d0fd068d598

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.hasCompactSupport_cutSchwartz
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
theorem solution (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) :
    HasCompactSupport ((cutSchwartz g hg hgcs f : V → ℂ)) := (hgcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right
