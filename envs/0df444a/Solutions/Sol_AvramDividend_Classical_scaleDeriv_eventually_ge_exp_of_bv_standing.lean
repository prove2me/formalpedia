-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_bv_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:04:36.17271+00:00
-- url     : https://prove2.me/submissions/104e646d-5afc-4bd7-bf8f-7474f17e3068

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Under bounded variation and the standing assumptions, the scale derivative
eventually dominates a strictly positive exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by
  have hac : X.ν ≪ volume :=
    standing_bv_levy_absolutely_continuous X hX hbv
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
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
