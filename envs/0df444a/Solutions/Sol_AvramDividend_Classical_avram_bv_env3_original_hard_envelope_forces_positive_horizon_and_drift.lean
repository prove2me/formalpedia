-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_hard_envelope_forces_positive_horizon_and_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:51:16.325964+00:00
-- url     : https://prove2.me/submissions/246c6e35-04bb-4150-9974-3c551fc4fda7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine BV complement forces both a positive horizon and a
    positive original process drift, including initial reserve at the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    0 < T ∧ 0 < X.drift := by
  have hcap :=
    avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hw_smooth hw_grad x hx hxc
  have hw : w 0 + x ≤ w x := hcap x ⟨hx, le_refl x⟩
  have hxw : x ≤ w x := by linarith
  have hstrict : w x < x + T * X.drift := lt_of_not_ge hEnvelope
  have hprod : 0 < T * X.drift := by linarith
  have hTpos : 0 < T := by
    by_contra hn
    have hz : T = 0 := le_antisymm (le_of_not_gt hn) hT
    simp [hz] at hprod
  have hdpos : 0 < X.drift := by
    by_contra hn
    have hdle : X.drift ≤ 0 := le_of_not_gt hn
    have hprod_le : T * X.drift ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hT hdle
    linarith
  exact ⟨hTpos, hdpos⟩
