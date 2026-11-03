-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:29:38.158288+00:00
-- url     : https://prove2.me/submissions/8c73ccc6-cc8b-4326-bfd6-0bff9b7e1bbb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    (∀ C : ℝ≥0∞,
      ENNReal.ofReal θ * valueFunctionLe X q C x ≤
        ENNReal.ofReal (Real.exp (θ * x))) ∧
    ENNReal.ofReal θ * valueFunction X q x ≤
      ENNReal.ofReal (Real.exp (θ * x)) := by
  have hcap (C : ℝ≥0∞) :
      ENNReal.ofReal θ * valueFunctionLe X q C x ≤
        ENNReal.ofReal (Real.exp (θ * x)) := by
    unfold valueFunctionLe
    rw [ENNReal.mul_iSup]
    refine iSup_le fun D => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hD => ?_
    simpa only [dividendValue] using
      (avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
        X x C D hD θ hθ q hq)
  refine ⟨hcap, ?_⟩
  rw [← valueFunctionLe_top_eq_valueFunction X q x]
  exact hcap ⊤
