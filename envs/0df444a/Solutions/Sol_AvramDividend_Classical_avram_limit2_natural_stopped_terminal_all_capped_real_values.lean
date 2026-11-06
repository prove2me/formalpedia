-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_natural_stopped_terminal_all_capped_real_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:04:43.588563+00:00
-- url     : https://prove2.me/submissions/9630ef79-a491-4433-850b-a438e9c15f63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Source-exact natural stopped cash and terminal budgets for every original
    capped policy give real L1 and both capped and top-cap value bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hBudget : ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in
            paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) + Terminal ω) ∂P)
          ≤ ENNReal.ofReal (w x)) :
    (∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ (x : ℝ), 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hPolicy : ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        dividendValue X q x D ≤ ENNReal.ofReal (w x) ∧
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x := by
    intro x hx hxc D hD
    have hCash : ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
      intro n
      obtain ⟨Terminal, hStopped⟩ := hBudget x hx hxc D hD n
      calc
        _ ≤ (∫⁻ ω, ((∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
          apply lintegral_mono
          intro ω
          exact le_add_of_nonneg_right bot_le
        _ ≤ ENNReal.ofReal (w x) := hStopped
    have hValue :
        dividendValue X q x D ≤ ENNReal.ofReal (w x) :=
      avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
        X q x D hD.1 (ENNReal.ofReal (w x)) hCash
    have hReal := avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
        X x D hD.1.1 q (w x) (hw x hx hxc) hValue
    exact ⟨hValue, hReal⟩
  have hCapped : ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc
    unfold valueFunctionLe
    refine iSup_le fun D => iSup_le fun hD => ?_
    exact (hPolicy x hx hxc D hD).1
  refine ⟨?_, hCapped, ?_⟩
  · intro x hx hxc D hD
    exact (hPolicy x hx hxc D hD).2
  · intro hTop x hx
    subst C
    simpa only [valueFunctionLe_top_eq_valueFunction] using hCapped x hx le_top
