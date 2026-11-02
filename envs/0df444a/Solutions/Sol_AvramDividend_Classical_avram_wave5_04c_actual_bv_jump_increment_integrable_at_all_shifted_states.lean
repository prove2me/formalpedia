-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_jump_increment_integrable_at_all_shifted_states
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:14:34.253473+00:00
-- url     : https://prove2.me/submissions/5c082081-0009-46a0-8888-57a7c2ecf2e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x z : ℝ) (hgen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (z + y) - w z) (Iio 0) X.ν := by
  let K : ℝ → ℝ → ℝ := fun t y => w (t + y) - w t
  let D : ℝ := |z - x|
  let C : ℝ := 2 * L * max 1 D
  have hKx : IntegrableOn (K x) (Iio 0) X.ν := by
    simpa only [K] using boundedVariation_full_negative_jump_increment_integrable
      X hBV w x hgen
  have hmeas (t : ℝ) : Measurable (K t) := by
    exact ((hwC1.continuous.measurable.comp
      (measurable_const.add measurable_id)).sub measurable_const)
  have hdmeas :
      AEStronglyMeasurable (fun y => K z y - K x y)
        (X.ν.restrict (Iio 0)) :=
    ((hmeas z).sub (hmeas x)).aestronglyMeasurable
  have hmajor : Integrable (fun y : ℝ => C * min 1 |y|)
      (X.ν.restrict (Iio 0)) := by
    change IntegrableOn (fun y : ℝ => C * min 1 |y|) (Iio 0) X.ν
    exact chat07_bv_negative_jump_scalar_majorant_integrable X hBV C
  have hmin (r : ℝ) (hr : 0 ≤ r) :
      min D r ≤ max 1 D * min 1 r := by
    have hD : 0 ≤ D := abs_nonneg _
    by_cases hr1 : r ≤ 1
    · have hmr : min 1 r = r := min_eq_right hr1
      rw [hmr]
      have ha : min D r ≤ r := min_le_right _ _
      have hb : 1 ≤ max 1 D := le_max_left _ _
      have hc : r ≤ max 1 D * r := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hb) hr]
      exact le_trans ha hc
    · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
      have hmr : min 1 r = 1 := min_eq_left hr1'
      rw [hmr]
      have hmax : D ≤ max 1 D := le_max_right _ _
      nlinarith [min_le_left D r]
  have hbound : ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
      ‖K z y - K x y‖ ≤ C * min 1 |y| := by
    filter_upwards [] with y
    have ha := avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
      w L hL hLip x z y
    have hb := hmin |y| (abs_nonneg y)
    have hc : 0 ≤ 2 * L := by positivity
    calc
      ‖K z y - K x y‖ =
          |(w (z + y) - w z) - (w (x + y) - w x)| := by
        simp only [K, Real.norm_eq_abs]
      _ ≤ 2 * L * min D |y| := by simpa only [D] using ha
      _ ≤ 2 * L * (max 1 D * min 1 |y|) :=
        mul_le_mul_of_nonneg_left hb hc
      _ = C * min 1 |y| := by ring
  have hdiff : Integrable (fun y => K z y - K x y)
      (X.ν.restrict (Iio 0)) := hmajor.mono' hdmeas hbound
  have hs := hKx.add hdiff
  have heq : (fun y : ℝ => w (z + y) - w z) =
      (fun y : ℝ => K x y + (K z y - K x y)) := by
    funext y
    dsimp [K]
    ring
  rw [heq]
  exact hs
