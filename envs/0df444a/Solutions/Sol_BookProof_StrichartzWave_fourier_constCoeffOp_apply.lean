-- Prove2me | solution 1 for BookProof.StrichartzWave.fourier_constCoeffOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:36:32.000797+00:00
-- url     : https://prove2.me/submissions/282ed9fa-4c2b-4023-831a-c6baccbab804

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.fourier_constCoeffOp_apply
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_fourier_secondDeriv_apply
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (w : ι → V) (κ : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (constCoeffOp c w κ f) : 𝓢(V, ℂ)) x
      = ((symbolFn c w κ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by

  have hlin : (𝓕 (constCoeffOp c w κ f) : 𝓢(V, ℂ))
      = (∑ i, (c i : ℂ) • (𝓕 (secondDeriv (w i) f) : 𝓢(V, ℂ))) + (κ : ℂ) • (𝓕 f : 𝓢(V, ℂ)) := by
    change fourierTransformCLM ℂ (constCoeffOp c w κ f) = _
    simp [constCoeffOp]
  rw [hlin]
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    fourier_secondDeriv_apply, symbolFn, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Finset.sum_mul, add_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring
