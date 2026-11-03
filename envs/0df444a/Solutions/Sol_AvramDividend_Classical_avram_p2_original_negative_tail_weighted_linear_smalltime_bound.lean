-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_negative_tail_weighted_linear_smalltime_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:25:57.169431+00:00
-- url     : https://prove2.me/submissions/944309d9-851f-410a-8a4d-6f3694d43810

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_deficit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_deficit_linear_smalltime_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual source negative-increment tail has an O(h) upper estimate
after multiplication by an explicit strictly positive band-dependent factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) *
          P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
        ENNReal.ofReal (C * h) := by
  obtain ⟨C, hCpos, hRate⟩ :=
    avram_p2_original_fourth_deficit_linear_smalltime_bound X
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hRate] with h hBound
  have hXm : Measurable (X.X (Real.toNNReal h)) :=
    (X.adapted (Real.toNNReal h)).mono (𝓕.le _) le_rfl
  have hMarkov :=
    avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound
      X (Real.toNNReal h) ε 1 hε (by norm_num) hXm
  have hIntegrable :
      Integrable (fun ω => (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) P :=
    avram_p2_original_fourth_deficit_integrable X (Real.toNNReal h)
  have hNonneg : 0 ≤ᵐ[P]
      (fun ω => (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) :=
    Filter.Eventually.of_forall (by intro ω; positivity)
  have hConversion :
      (∫⁻ ω, ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) =
      ENNReal.ofReal
        (∫ ω, (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hIntegrable hNonneg).symm
  calc
    ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) *
        P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
      ∫⁻ ω, ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P := by
          simpa only [one_mul, neg_one_mul] using hMarkov
    _ = ENNReal.ofReal
        (∫ ω, (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) :=
      hConversion
    _ ≤ ENNReal.ofReal (C * h) := ENNReal.ofReal_le_ofReal hBound
