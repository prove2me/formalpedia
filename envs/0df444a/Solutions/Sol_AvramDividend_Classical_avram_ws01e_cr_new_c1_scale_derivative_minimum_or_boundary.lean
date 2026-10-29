-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_c1_scale_derivative_minimum_or_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:04:06.705506+00:00
-- url     : https://prove2.me/submissions/7ffeca6f-8a66-477a-acd0-6e45727b29f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Full Standing plus C1 regularity gives the interior-minimum or zero-right-liminf
    dichotomy without an additional corrected-exit hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hW1 : 0 < W 1 := hpos 1 (by norm_num)
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have htop : Tendsto (deriv W) atTop atTop :=
    scale_deriv_tendsto_atTop_of_normalized_monotone
      W φ hφ hW1 htilt hdiff
  simpa only [derivZeroPlus] using
    (positive_minimum_or_right_liminf_of_tendsto_atTop
      (deriv W) hcont htop)
