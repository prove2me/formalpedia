-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:55:06.990689+00:00
-- url     : https://prove2.me/submissions/85260f9b-4402-4426-aaf4-b7f791417a57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_away_zero

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
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by
  obtain ⟨r, Cnear, hr, hrle, hCnear, hnear⟩ :=
    scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
      X q W hW a x hx hC2
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    scaleFunction_generatorIntegrand_min_sq_bound_away_zero
      X q W hW x r hx.1 hr
  let C : ℝ := max Cnear Cfar
  have hC : 0 ≤ C := by
    dsimp [C]
    exact hCnear.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy0
  by_cases hyr : y ≤ -r
  · have hkernel : 0 ≤ min 1 (y ^ 2) := by positivity
    calc
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖
          ≤ Cfar * min 1 (y ^ 2) := hfar y hy0 hyr
      _ ≤ C * min 1 (y ^ 2) :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_max_right _ _) hkernel
  · have hyr' : -r < y := lt_of_not_ge hyr
    have hyNear : y ∈ Ioo (-r) 0 := ⟨hyr', hy0⟩
    have hr1 : r ≤ 1 := hrle.trans (min_le_right x 1)
    have hym1 : -1 < y := by linarith
    have hy1 : y < 1 := by linarith
    have hprod : 0 < (1 - y) * (1 + y) :=
      mul_pos (by linarith) (by linarith)
    have hy2le : y ^ 2 ≤ 1 := by nlinarith
    have hmin : min 1 (y ^ 2) = y ^ 2 :=
      min_eq_right hy2le
    calc
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖
          ≤ Cnear * y ^ 2 := hnear y hyNear
      _ ≤ C * y ^ 2 :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_max_left _ _) (sq_nonneg y)
      _ = C * min 1 (y ^ 2) := by rw [hmin]
