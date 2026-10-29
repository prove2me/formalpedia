-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_c1_derivative_growth_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:01:11.631193+00:00
-- url     : https://prove2.me/submissions/c906c6cf-1c5a-4c57-a08c-7391f6c5b698

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  obtain ⟨hpos, φ, hφ, hmono⟩ := AvramDividend.Classical.scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hd : ∀ x : ℝ, 0 < x → φ * W x ≤ deriv W x := fun x hx =>
    AvramDividend.Classical.normalized_derivative_lower_bound φ x hmono hx
      ((hreg.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hx))
  obtain ⟨c, hc, hev⟩ := AvramDividend.Classical.normalized_eventual_derivative_growth φ 1 hφ one_pos
    (hpos 1 one_pos) hmono hd
  exact ⟨φ, c, hφ, hc, hev⟩
