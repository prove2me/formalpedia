-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_uniformBound_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T03:20:17.533989+00:00
-- url     : https://prove2.me/submissions/3ccc8384-bd14-48f6-83d6-f3946ca80468

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive

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
    (x : ℝ) (hx : 0 < x) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := by
  -- The scale function does not increase to the left, so the increment
  -- `W (x + y) - W x` is bounded by `W x` for every `y < 0`.
  have hdiff : ∀ y : ℝ, y < 0 → |W (x + y) - W x| ≤ W x := by
    intro y hy
    have hs := scaleFunction_shift_bounds_of_nonpositive
      X q W hW x y hx.le (le_of_lt hy)
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1]
  -- The compensation term is bounded by `|deriv W x|`, because the
  -- compensation indicator is bounded by `1`.
  have hcomp : ∀ y : ℝ, y < 0 →
      |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y| ≤ |deriv W x| := by
    intro y hy
    have hind : |y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y| ≤ 1 := by
      by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
      · have habs : |y| < 1 := abs_lt.mpr hyI
        simpa [Set.indicator, hyI] using habs.le
      · simp [Set.indicator, hyI]
    rw [mul_assoc, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hind (abs_nonneg (deriv W x))
  -- Combine the two estimates.
  let B : ℝ := W x + |deriv W x|
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hWx0 : 0 ≤ W x := hW.2.1 x hx.le
    positivity
  refine ⟨B, hB0, ?_⟩
  intro y hy
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [Real.norm_eq_abs]
  calc
    |W (x + y) - W x - deriv W x * y *
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y|
        ≤ |W (x + y) - W x| +
            |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y| := abs_sub _ _
    _ ≤ W x + |deriv W x| := add_le_add (hdiff y hy) (hcomp y hy)
    _ = B := rfl
