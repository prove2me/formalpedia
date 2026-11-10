-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys16_original_firstjump_contact_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:07:35.477186+00:00
-- url     : https://prove2.me/submissions/63868a9a-1486-42e1-b62e-2aee06ba5e6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → t ≤ H →
      (t : WithTop ℝ≥0) <
        (⨅ v : ℝ≥0,
          if 0 < v ∧ X.X v ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v < 0
          then (v : WithTop ℝ≥0) else ⊤) →
      (∀ v : ℝ≥0, s ≤ v → v ≤ t →
        riskProcess X x D v ω -
          (rightLimit D v ω - D v ω) = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ r in Ioc (s : ℝ) (t : ℝ), f r
          ∂(dividendMeasure D ω)) =
        (∫⁻ r in Ioc (s : ℝ) (t : ℝ), f r
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [
    avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
      X hBV hFinite hDrift x C D hD H hH
  ] with ω hω
  intro s t hst htH hBefore hZero f
  apply hω s t hst htH hZero
  intro v hv
  have hvpos : (0 : ℝ≥0) < v :=
    lt_of_le_of_lt (by positivity : (0 : ℝ≥0) ≤ s) hv.1
  have hvle : (v : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
    exact_mod_cast hv.2
  exact avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
    X ω v hvpos (lt_of_le_of_lt hvle hBefore)
