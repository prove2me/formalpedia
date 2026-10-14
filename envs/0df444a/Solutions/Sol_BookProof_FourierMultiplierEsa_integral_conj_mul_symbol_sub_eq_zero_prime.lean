-- Prove2me | solution 1 for BookProof.FourierMultiplierEsa.integral_conj_mul_symbol_sub_eq_zero_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:23.64015+00:00
-- url     : https://prove2.me/submissions/e7f7b7cb-c5d4-48b5-9c48-1cb8784a2f7a

-- Generated from ChapterFourierMultiplierEsa.lean — solution of BookProof.FourierMultiplierEsa.integral_conj_mul_symbol_sub_eq_zero'
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left_fourier
import Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterStrichartzWave
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
theorem solution (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ)
    (hP : ∀ (f : 𝓢(V, ℂ)) (x : V),
      (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x)
    (z : ℂ) (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 P v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (ψ x) * (((σ x : ℝ) : ℂ) - z) *
      ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0 := by

  set g : Lp ℂ 2 (volume : Measure V) := 𝓕 u with hg
  set f : 𝓢(V, ℂ) := 𝓕⁻ ψ with hfdef
  have hf : (𝓕 f : 𝓢(V, ℂ)) = ψ := fourier_fourierInv_eq ψ
  have h1 := hu (schwartzEquiv V f)
  rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left_fourier, inner_toLp_left_fourier] at h1
  have hL : ∫ x, (starRingEnd ℂ) ((𝓕 (P f) : 𝓢(V, ℂ)) x) * (g x)
      = ∫ x, ((σ x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hP, hf, map_mul, Complex.conj_ofReal]
    ring
  rw [hL, hf] at h1
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (ψ x) * (g x)) (volume : Measure V) :=
    integrable_conj_schwartz_mul ψ g
  have hint2 : Integrable
      (fun x => ((σ x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x))) (volume : Measure V) := by
    have := integrable_conj_schwartz_mul (𝓕 (P f) : 𝓢(V, ℂ)) g
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hP, hf, map_mul, Complex.conj_ofReal]
    ring
  have hcomb : ∫ x, (((σ x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x))
      - z * ((starRingEnd ℂ) (ψ x) * (g x))) = 0 := by
    rw [integral_sub hint2 (hint1.const_mul z), MeasureTheory.integral_const_mul, h1]
    ring
  rw [← hcomb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring
