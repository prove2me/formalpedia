-- Prove2me | solution 1 for BookProof.FourierMultiplierEsa.fourier_mixedOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:15:44.036763+00:00
-- url     : https://prove2.me/submissions/8fe99261-c678-40a5-944e-1cc529cd39eb

-- Generated from ChapterFourierMultiplierEsa.lean — solution of BookProof.FourierMultiplierEsa.fourier_mixedOp_apply
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_firstOrderOp_apply
import Theorems.Thm_BookProof_StrichartzWave_fourier_constCoeffOp_apply
open BookProof.FourierMultiplierEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (a c : ι → ℝ) (w : ι → V) (κ : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (mixedOp a c w κ f) : 𝓢(V, ℂ)) x
      = ((mixedSymbolFn a c w κ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by

  have hlin : (𝓕 (mixedOp a c w κ f) : 𝓢(V, ℂ))
      = (𝓕 (constCoeffOp c w κ f) : 𝓢(V, ℂ)) + (𝓕 (firstOrderOp a w f) : 𝓢(V, ℂ)) := by
    change fourierTransformCLM ℂ (mixedOp a c w κ f) = _
    simp [mixedOp]
  rw [hlin]
  simp only [SchwartzMap.add_apply, fourier_constCoeffOp_apply, fourier_firstOrderOp_apply,
    mixedSymbolFn, Complex.ofReal_add]
  ring
