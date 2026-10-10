-- Prove2me | solution 1 for BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:02:55.482993+00:00
-- url     : https://prove2.me/submissions/d0faef44-d713-402f-b261-0512ee570ecd

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line
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
theorem solution {W θ : V → ℝ} {m : V}
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) (x : V) :
    HasDerivAt (fun t : ℝ => phaseFun θ (x + t • m))
      (phaseFun θ x * (Complex.I * ((-(W x) : ℝ) : ℂ))) 0 := by

  have h1 : HasDerivAt (fun t : ℝ => ((θ (x + t • m) : ℝ) : ℂ)) (((-(W x) : ℝ) : ℂ)) 0 :=
    (hθd x).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * ((θ (x + t • m) : ℝ) : ℂ))
      (Complex.I * ((-(W x) : ℝ) : ℂ)) 0 := h1.const_mul _
  simpa [phaseFun] using h2.cexp
