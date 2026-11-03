-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_standing_positive_discount_all_optimal_values_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:58:58.59245+00:00
-- url     : https://prove2.me/submissions/2492bcab-ecba-4ca4-8b1c-b9443c4df20b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (x : ℝ) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by
  obtain ⟨φ, hφ, hψ⟩ :=
    avram_wave4_05_source_positive_psi_root_of_standing X hX q hq
  exact avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
    X x φ hφ q (le_of_eq hψ)
