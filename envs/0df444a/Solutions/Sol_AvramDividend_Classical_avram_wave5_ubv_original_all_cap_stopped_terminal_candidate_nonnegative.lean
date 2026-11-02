-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:44:52.967461+00:00
-- url     : https://prove2.me/submissions/307fce64-94bd-4655-b4c6-13cdf241eaef

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 ≤ w (riskProcess X x D t ω) := by
  intro ω t
  by_cases hy : 0 ≤ riskProcess X x D t ω
  · have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
      admissibleLe_riskProcess_le_cap_all_times X x C D hD hxc ω t
    have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hw_cont hw_smooth hw_grad 0 (riskProcess X x D t ω)
      (le_refl (0 : ℝ)) hy hcap
    linarith
  · have hneg : riskProcess X x D t ω < 0 := lt_of_not_ge hy
    rw [hw_neg _ hneg]
