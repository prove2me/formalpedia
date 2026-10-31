-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_corrected_exit_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:58:07.37774+00:00
-- url     : https://prove2.me/submissions/084f44f8-a995-4d10-ba45-14cb2c556492

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_ratio_exp_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Uniform exponential decay of the genuine discounted two-sided
upward exit reward over all starting reserves in a bounded interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ R a : ℝ, 0 ≤ R → R + 1 ≤ a →
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        twoSidedExitExpectationCorrected X q a x) ≤
        ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))) := by
  obtain ⟨φ, hφ, hratio⟩ :=
    avram_wave3_02_esscher_ratio_exp_bound X hX q hq W hW
  obtain ⟨hWpos, _⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  refine ⟨φ, hφ, ?_⟩
  intro R a hR hRa
  have ha : 0 < a := by linarith
  have hWa : 0 ≤ W a := le_of_lt (hWpos a ha)
  have hRpos : 0 < R + 1 := by linarith
  have hRratio := hratio (R + 1) a hRpos hRa
  refine iSup_le fun x => ?_
  refine iSup_le fun hx => ?_
  have hxa : x ≤ a := by linarith [hx.2]
  rw [two_sided_exit_before_ruin_identity_corrected
    X hX q hq W hW a x ha hx.1 hxa]
  have hdiv : W x / W a ≤ W (R + 1) / W a :=
    div_le_div_of_nonneg_right (hmono (by linarith [hx.2])) hWa
  exact (ENNReal.ofReal_le_ofReal hdiv).trans
    (ENNReal.ofReal_le_ofReal hRratio)
