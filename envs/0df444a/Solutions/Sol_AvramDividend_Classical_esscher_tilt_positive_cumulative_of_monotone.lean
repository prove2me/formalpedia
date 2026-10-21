-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_positive_cumulative_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:40:26.371512+00:00
-- url     : https://prove2.me/submissions/d03d62c6-14a2-4852-8e1f-0ff30c0c317d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_stieltjes_cumulative_of_monotone_continuous_zero_left
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Once the stochastic Esscher monotonicity is known, the scale factor has a positive Stieltjes cumulative measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (φ : ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∃ β : Measure ℝ,
      (∀ x : ℝ, β (Iic x) =
        ENNReal.ofReal (Real.exp (-φ * x) * W x)) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-φ * x) * W x
  have hcontW : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have hcont : Continuous f := by
    dsimp [f]
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul hcontW
  have hneg : ∀ x : ℝ, x < 0 → f x = 0 := by
    intro x hx
    simp [f, hW.1 x hx]
  have hposF : ∀ x : ℝ, 0 < x → 0 < f x := by
    intro x hx
    exact mul_pos (Real.exp_pos _) (hpos x hx)
  have hnonpos : ∀ x : ℝ, x ≤ 0 → f x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact hneg x hlt
    · subst x
      simp [f, hzero]
  have hmonoF : Monotone f := by
    intro x y hxy
    by_cases hy : y ≤ 0
    · rw [hnonpos x (le_trans hxy hy), hnonpos y hy]
    · have hypos : 0 < y := lt_of_not_ge hy
      by_cases hx : 0 < x
      · exact htilt hx hypos hxy
      · rw [hnonpos x (le_of_not_gt hx)]
        exact le_of_lt (hposF y hypos)
  exact stieltjes_cumulative_of_monotone_continuous_zero_left
    f hmonoF hcont hneg hposF
