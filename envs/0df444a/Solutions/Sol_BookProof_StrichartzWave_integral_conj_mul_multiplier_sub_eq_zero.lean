-- Prove2me | solution 1 for BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:27:41.241057+00:00
-- url     : https://prove2.me/submissions/cd629533-972f-4a57-9797-d0c64218c358
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_fourier_multiplierOp_apply
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left_fourier
import Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V → ℝ) (hm : Function.HasTemperateGrowth m)
    (z : ℂ) (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 (multiplierOp m) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (ψ x) * (((m x : ℝ) : ℂ) - z) *
      ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0 := by

  set g : Lp ℂ 2 (volume : Measure V) := 𝓕 u with hg
  set f : 𝓢(V, ℂ) := 𝓕⁻ ψ with hfdef
  have hf : (𝓕 f : 𝓢(V, ℂ)) = ψ := fourier_fourierInv_eq ψ
  have h1 := hu (schwartzEquiv V f)
  rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left_fourier, inner_toLp_left_fourier] at h1
  have hL : ∫ x, (starRingEnd ℂ) ((𝓕 (multiplierOp m f) : 𝓢(V, ℂ)) x) * (g x)
      = ∫ x, ((m x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fourier_multiplierOp_apply hm, hf, map_mul, Complex.conj_ofReal]
    ring
  rw [hL, hf] at h1
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (ψ x) * (g x)) (volume : Measure V) :=
    integrable_conj_schwartz_mul ψ g
  have hint2 : Integrable (fun x => ((m x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x)))
      (volume : Measure V) := by
    have := integrable_conj_schwartz_mul (𝓕 (multiplierOp m f) : 𝓢(V, ℂ)) g
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [fourier_multiplierOp_apply hm, hf, map_mul, Complex.conj_ofReal]
    ring
  have hcomb : ∫ x, (((m x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (g x))
      - z * ((starRingEnd ℂ) (ψ x) * (g x))) = 0 := by
    rw [integral_sub hint2 (hint1.const_mul z), MeasureTheory.integral_const_mul, h1]
    ring
  rw [← hcomb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring
