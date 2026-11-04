-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:47:10.82439+00:00
-- url     : https://prove2.me/submissions/ab0815b6-106f-4c22-ab29-948633ce4393

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_negative_mark_piecewise_envelope_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Bound the actual BV negative Lévy generator integral using the independently
source-proved integrable near-linear/far-constant physical mark envelope. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (w : ℝ → ℝ) (hwMeas : Measurable w)
  (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (hMass : X.ν (Iic (-a / 2)) < ⊤) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Icc a b,
    |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| ≤ M := by
  let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z)
  have hG : IntegrableOn G (Iio 0) X.ν :=
    avram_wave8_22_original_BV_physical_negative_mark_piecewise_envelope_integrable
      X hBV a L R ha ha2 hL hR
  have hGnonneg : ∀ᵐ z ∂(X.ν.restrict (Iio 0)), 0 ≤ G z := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    by_cases hcut : z ≤ -a / 2
    · have hconst : 0 ≤ 2 * R := mul_nonneg (by norm_num) hR
      simpa only [G, if_pos hcut] using hconst
    · have hzlt : z < 0 := hz
      have hzneg : 0 ≤ -z := neg_nonneg.mpr (le_of_lt hzlt)
      simpa only [G, if_neg hcut] using mul_nonneg hL hzneg
  have hMnonneg : 0 ≤ ∫ z in Iio 0, G z ∂X.ν :=
    integral_nonneg_of_ae hGnonneg
  refine ⟨∫ z in Iio 0, G z ∂X.ν, hMnonneg, ?_⟩
  intro y hy
  have hDom : ∀ᵐ z ∂(X.ν.restrict (Iio 0)),
      |w (y + z) - w y| ≤ G z := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    obtain ⟨hSmall, hLarge⟩ :=
      avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
        w a b L R ha hab hL hR hLip hWbound y z hy hz
    by_cases hcut : z ≤ -a / 2
    · simpa [G, hcut] using hLarge hcut
    · have hzsmall : -a / 2 < z := lt_of_not_ge hcut
      have hzlt : z < 0 := hz
      have hBound : |w (y + z) - w y| ≤ L * (-z) := by
        calc
          |w (y + z) - w y| ≤ L * |z| := hSmall hzsmall
          _ = L * (-z) := by rw [abs_of_neg hzlt]
      simpa only [G, if_neg hcut] using hBound
  have hFmeas : Measurable (fun z : ℝ => w (y + z) - w y) :=
    (hwMeas.comp (measurable_const.add measurable_id)).sub measurable_const
  have hFint : IntegrableOn (fun z : ℝ => w (y + z) - w y) (Iio 0) X.ν := by
    apply hG.mono' hFmeas.aestronglyMeasurable
    filter_upwards [hDom, hGnonneg] with z hz hz0
    simpa [Real.norm_eq_abs, abs_of_nonneg hz0] using hz
  have hFabs : Integrable (fun z : ℝ => |w (y + z) - w y|)
      (X.ν.restrict (Iio 0)) := by
    simpa only [Real.norm_eq_abs] using hFint.norm
  have hNorm : |∫ z in Iio 0, w (y + z) - w y ∂X.ν| ≤
      ∫ z in Iio 0, |w (y + z) - w y| ∂X.ν := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := X.ν.restrict (Iio 0))
        (f := fun z : ℝ => w (y + z) - w y))
  have hMono :
      (∫ z in Iio 0, |w (y + z) - w y| ∂X.ν) ≤
      ∫ z in Iio 0, G z ∂X.ν :=
    integral_mono_ae hFabs hG hDom
  exact hNorm.trans hMono
