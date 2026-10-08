-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:50:43.294982+00:00
-- url     : https://prove2.me/submissions/d377d785-567a-499e-b457-9f3ede74eb6c

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
  obtain ⟨r, Cn, hr, hrle, hCn, hnear⟩ :=
    scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
      X q W hW a x hx hC2
  obtain ⟨Cf, hCf, hfar⟩ :=
    scaleFunction_generatorIntegrand_min_sq_bound_away_zero
      X q W hW x r hx.1 hr
  refine ⟨max Cn Cf, ?_, ?_⟩
  · exact hCn.trans (le_max_left Cn Cf)
  · intro y hy0
    have hmin0 : 0 ≤ min 1 (y ^ 2) := by positivity
    by_cases hyr : y ≤ -r
    · exact (hfar y hy0 hyr).trans
        (mul_le_mul_of_nonneg_right (le_max_right Cn Cf) hmin0)
    · have hynear : y ∈ Ioo (-r) 0 := ⟨lt_of_not_ge hyr, hy0⟩
      have hr1 : r ≤ 1 := hrle.trans (min_le_right x 1)
      have hyneg1 : -1 ≤ y := by linarith
      have hprod : (y - 1) * (y + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have hy2le : y ^ 2 ≤ 1 := by nlinarith
      rw [min_eq_right hy2le]
      exact (hnear y hynear).trans
        (mul_le_mul_of_nonneg_right (le_max_left Cn Cf) (sq_nonneg y))
