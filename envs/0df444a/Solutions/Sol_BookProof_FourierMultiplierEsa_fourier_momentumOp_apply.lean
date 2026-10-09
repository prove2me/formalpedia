-- Prove2me | solution 1 for BookProof.FourierMultiplierEsa.fourier_momentumOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:14:50.569479+00:00
-- url     : https://prove2.me/submissions/27ee3efe-533e-4338-ab3d-6e00ab3761c7

-- Generated from ChapterFourierMultiplierEsa.lean — solution of BookProof.FourierMultiplierEsa.fourier_momentumOp_apply
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
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
theorem solution (f : 𝓢(V, ℂ)) (m : V) (x : V) :
    (𝓕 (momentumOp m f) : 𝓢(V, ℂ)) x
      = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by

  have h : (inner ℝ · m : V → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  have hlin : (𝓕 (momentumOp m f) : 𝓢(V, ℂ))
      = (-Complex.I) • (𝓕 (∂_{m} f : 𝓢(V, ℂ)) : 𝓢(V, ℂ)) := by
    change fourierTransformCLM ℂ (momentumOp m f) = _
    simp [momentumOp]
  rw [hlin]
  simp only [SchwartzMap.smul_apply, smul_eq_mul, fourier_lineDerivOp_eq, h, smulLeftCLM_apply,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [show (-Complex.I) * (((2 : ℂ) * Real.pi * Complex.I) *
      (((inner ℝ x m : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x))
      = (-(Complex.I * Complex.I)) * ((2 : ℂ) * Real.pi * ((inner ℝ x m : ℝ) : ℂ) *
        (𝓕 f : 𝓢(V, ℂ)) x) by ring]
  rw [show Complex.I * Complex.I = -1 from Complex.I_mul_I]
  ring
