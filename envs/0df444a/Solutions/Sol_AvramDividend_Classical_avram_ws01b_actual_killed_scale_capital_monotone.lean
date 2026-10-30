-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_killed_scale_capital_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:05:27.30866+00:00
-- url     : https://prove2.me/submissions/c44e36d4-2bbf-430c-98a1-8f0a601d0641

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- For the actual Lévy source and continuous-window killing, the discounted
nonnegative scale reward is monotone in the initial reserve. This is the
source-specific spatial squeeze needed to uniformise good times after
Wiener–Hopf spatial Laplace uniqueness, including reserve zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (t : ℝ≥0) (x y : ℝ) (hxy : x ≤ y) :
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))
      else (0 : ℝ≥0∞) ∂P) ≤
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ t → 0 ≤ y + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
          W (y + X.X t ω))
      else (0 : ℝ≥0∞) ∂P) := by
  classical
  apply lintegral_mono
  intro ω
  by_cases hx : ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω
  · have hy : ∀ v : ℝ≥0, v ≤ t → 0 ≤ y + X.X v ω := by
      intro v hv
      exact le_trans (hx v hv) (by
        simpa only [add_comm] using (add_le_add_right hxy (X.X v ω)))
    simp only [if_pos hx, if_pos hy]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left
    · exact (scaleFunction_monotone X q W hW) (by
        simpa only [add_comm] using (add_le_add_right hxy (X.X t ω)))
    · exact le_of_lt (Real.exp_pos _)
  · simp only [if_neg hx]
    exact bot_le
