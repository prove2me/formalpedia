-- Prove2me | solution 1 for BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:14:51.554812+00:00
-- url     : https://prove2.me/submissions/ee80f3ee-0924-48f1-964a-1aa02c6fafd5

-- Generated from ChapterFourierMultiplierEsa.lean — solution of BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_momentumOp_apply
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
theorem solution (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (firstOrderOp c w f) : 𝓢(V, ℂ)) x
      = ((foSymbolFn c w x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by

  have hlin : (𝓕 (firstOrderOp c w f) : 𝓢(V, ℂ))
      = ∑ i, (c i : ℂ) • (𝓕 (momentumOp (w i) f) : 𝓢(V, ℂ)) := by
    change fourierTransformCLM ℂ (firstOrderOp c w f) = _
    simp [firstOrderOp]
  rw [hlin]
  simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    fourier_momentumOp_apply, foSymbolFn, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring