-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_cr_new_c1_derivative_growth_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:01:13.558153+00:00
-- url     : https://prove2.me/submissions/07244a9c-d331-4983-9ee5-a58c22554d18

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Positive-axis C1 regularity alone upgrades the genuine tilted scale monotonicity
    to a quantitative exponential lower bound on the derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  have hd : ∀ x : ℝ, 0 < x → φ * W x ≤ deriv W x := by
    intro x hx
    exact normalized_derivative_lower_bound φ x htilt hx (hdiff x hx)
  obtain ⟨c, hc, hevent⟩ :=
    normalized_eventual_derivative_growth (W := W) φ 1 hφ
      (by norm_num) (hpos 1 (by norm_num)) htilt hd
  exact ⟨φ, c, hφ, hc, hevent⟩
