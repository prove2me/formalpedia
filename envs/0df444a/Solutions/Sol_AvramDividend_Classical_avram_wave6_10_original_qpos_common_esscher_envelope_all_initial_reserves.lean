-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:52:51.57699+00:00
-- url     : https://prove2.me/submissions/9c338687-9427-4bc0-add0-4304a66b7644

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x : ℝ,
      (∀ C : ℝ≥0∞,
        ENNReal.ofReal θ * valueFunctionLe X q C x ≤
          ENNReal.ofReal (Real.exp (θ * x))) ∧
      ENNReal.ofReal θ * valueFunction X q x ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by
  obtain ⟨θ, hθ, hψ⟩ :=
    avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount X q hq
  refine ⟨θ, hθ, ?_⟩
  intro x
  exact avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
    X x θ hθ q (le_of_lt hψ)
