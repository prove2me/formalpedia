-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_positive_cap_bv_preruin_candidate_dominates_actual_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:28:47.860973+00:00
-- url     : https://prove2.me/submissions/75b97cb8-af92-435f-9747-18af0abaed70

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At every original pre-ruin time, including time zero, the corrected
positive-cap BV candidate dominates the actual original controlled reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D t ω ∧
        riskProcess X x D t ω ≤ w (riskProcess X x D t ω) := by
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x C hxc D hD
  intro ω t hruin
  obtain ⟨hy0, hyC⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω t hruin
  have hsec :=
    avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad
      0 (riskProcess X x D t ω)
      (le_refl (0 : ℝ)) hy0 hyC
  constructor
  · exact hy0
  · linarith
