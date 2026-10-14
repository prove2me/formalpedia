-- Prove2me | solution 1 for DbarRegularity.fourierTransformL2_ae_eq_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T14:43:39.124609+00:00
-- url     : https://prove2.me/submissions/fe103e0b-bb58-4c97-9f45-2c8d75a8f628

import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff



namespace DbarRegularity

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal ContDiff

/-- On `L¹ ∩ L²`, the `L²` Fourier transform agrees almost everywhere with the Fourier integral. -/
theorem fourierTransformL2_ae_eq_fourier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (g : E → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    (Lp.fourierTransformₗᵢ E ℂ (hg2.toLp g) : E → ℂ) =ᵐ[volume] 𝓕 g := by
  set h := Lp.fourierTransformₗᵢ E ℂ (hg2.toLp g)
  have key : ∀ φ : 𝓢(E, ℂ), ∫ x, φ x • (h : E → ℂ) x = ∫ x, φ x • 𝓕 g x := by
    intro φ
    have h1 : ∫ x, φ x • (h : E → ℂ) x = Lp.toTemperedDistribution h φ := by
      rw [Lp.toTemperedDistribution_apply]
    have h2 : Lp.toTemperedDistribution h = 𝓕 (Lp.toTemperedDistribution (hg2.toLp g)) := by
      rw [Lp.fourier_toTemperedDistribution_eq]; rfl
    rw [h1, h2, TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
    have h3 : ∫ x, (𝓕 φ) x • (hg2.toLp g : E → ℂ) x = ∫ x, (𝓕 φ) x • g x := by
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with x hx
      rw [hx]
    rw [h3, fourier_coe]
    have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
      (L := innerₗ E) (e := Real.fourierChar) Real.continuous_fourierChar
      continuous_inner φ.integrable hg1
    simp only [smul_eq_mul] at this ⊢
    rw [show (𝓕 (φ : E → ℂ)) = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) φ
      from rfl, this]
    have hflip : (innerₗ E).flip = innerₗ E := by
      ext x y; simp [real_inner_comm]
    rw [hflip]; rfl
  have hcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg1
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp h).locallyIntegrable (by norm_num)
  · exact hcont.locallyIntegrable
  · intro ψ hψ hψc
    have hc : HasCompactSupport (fun x => (ψ x : ℂ)) := hψc.comp_left Complex.ofReal_zero
    have hd : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
    have := key (hc.toSchwartzMap hd)
    simpa [Complex.real_smul] using this

end DbarRegularity

open DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (g : E → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    (Lp.fourierTransformₗᵢ E ℂ (hg2.toLp g) : E → ℂ) =ᵐ[volume] 𝓕 g :=
  fourierTransformL2_ae_eq_fourier g hg1 hg2
