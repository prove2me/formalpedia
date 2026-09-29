-- Prove2me | solution 1 for BookProof.StrichartzWave.integral_conj_mul_symbol_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:37:43.214617+00:00
-- url     : https://prove2.me/submissions/6f7257f4-3ebd-4d47-af21-f58751b27a77

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.integral_conj_mul_symbol_sub_eq_zero
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_fourier_constCoeffOp_apply
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left_fourier
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (w : ι → V) (κ : ℝ) (z : ℂ)
    (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 (constCoeffOp c w κ) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (ψ x) * (((symbolFn c w κ x : ℝ) : ℂ) - z) *
      ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0 := by

  set g : Lp ℂ 2 (volume : Measure V) := 𝓕 u with hg
  set f : 𝓢(V, ℂ) := 𝓕⁻ ψ with hfdef
  have hf : (𝓕 f : 𝓢(V, ℂ)) = ψ := fourier_fourierInv_eq ψ
  have h1 := hu (schwartzEquiv V f)
  rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left_fourier, inner_toLp_left_fourier] at h1
  -- rewrite both integrands
  have hL : ∫ x, (starRingEnd ℂ) ((𝓕 (constCoeffOp c w κ f) : 𝓢(V, ℂ)) x) * (g x)
      = ∫ x, ((symbolFn c w κ x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fourier_constCoeffOp_apply, hf, map_mul, Complex.conj_ofReal]
    ring
  rw [hL, hf] at h1
  -- integrability of the two pieces
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (ψ x) * (g x)) (volume : Measure V) :=
    integrable_conj_schwartz_mul ψ g
  have hint2 : Integrable
      (fun x => ((symbolFn c w κ x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x)))
      (volume : Measure V) := by
    have := integrable_conj_schwartz_mul (𝓕 (constCoeffOp c w κ f) : 𝓢(V, ℂ)) g
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [fourier_constCoeffOp_apply, hf, map_mul, Complex.conj_ofReal]
    ring
  have hcomb : ∫ x, (((symbolFn c w κ x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x))
      - z * ((starRingEnd ℂ) (ψ x) * (g x))) = 0 := by
    rw [integral_sub hint2 (hint1.const_mul z), MeasureTheory.integral_const_mul, h1]
    ring
  rw [← hcomb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring
