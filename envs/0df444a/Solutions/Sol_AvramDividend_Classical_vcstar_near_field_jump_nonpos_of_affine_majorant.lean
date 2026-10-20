-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_field_jump_nonpos_of_affine_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:04:58.575462+00:00
-- url     : https://prove2.me/submissions/496d01b7-adfa-4b0f-91c1-1ec80da85613

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hmono : Monotone (vcstar W))
    (hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤
        z - (cstar W).toReal + vcstar W (cstar W).toReal)
    (x : ℝ)
    (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hbound : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hvalx : vcstar W x = x - a + vcstar W a := by
    have hx0 : ¬ x < 0 := not_lt.mpr (le_trans ha (le_of_lt hx))
    have hxa : ¬ x ≤ a := not_le.mpr hx
    have ha0 : ¬ a < 0 := not_lt.mpr ha
    change barrierValue W a x =
      x - a + barrierValue W a a
    simp only [barrierValue, if_neg hx0, if_neg hxa,
      if_neg ha0, if_pos le_rfl]
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  have hjump : (∫ y in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Iio
    intro y hy
    have hyneg : y < 0 := hy
    by_cases hlarge : y ≤ -1
    · have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
        intro hmem
        exact (not_lt_of_ge hlarge) hmem.1
      have hxy : x + y ≤ x := by linarith
      have hm := hmono hxy
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp [Set.indicator_of_notMem hnot]
      linarith
    · have hy1 : -1 < y := lt_of_not_ge hlarge
      have hz0 : 0 ≤ x + y := by linarith
      by_cases hbelow : x + y ≤ a
      · have hb := hchord (x + y) hz0 hbelow
        unfold SpectrallyNegativeLevy.generatorIntegrand
        have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, by linarith⟩
        simp only [Set.indicator_of_mem hmem, Pi.one_apply]
        rw [hder, hvalx]
        linarith
      · have hz : a < x + y := lt_of_not_ge hbelow
        have hz0' :
            SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y = 0 := by
          change SpectrallyNegativeLevy.generatorIntegrand
            (barrierValue W a) x y = 0
          exact barrier_generatorIntegrand_zero_small_negative_jump_above
            W a x y ha hx hz hy1 hyneg
        exact le_of_eq hz0'
  refine ⟨vcstar_generatorIntegrable_strictly_above_real_cstar
    X q W hW x hx, ?_⟩
  rw [vcstar_generator_above_eq_drift_add_jump X W x hx]
  linarith