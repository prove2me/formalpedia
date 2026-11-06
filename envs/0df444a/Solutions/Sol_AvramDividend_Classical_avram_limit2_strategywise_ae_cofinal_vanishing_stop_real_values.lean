-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_strategywise_ae_cofinal_vanishing_stop_real_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:27:26.315506+00:00
-- url     : https://prove2.me/submissions/914f6f17-07d9-408b-b331-6f11dd15968a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strategy-dependent a.e.-cofinal original clocks with vanishing errors
    imply real perpetual cash bounds and capped/top value comparisons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ σ : ℕ → Ω → ℝ≥0∞,
          (∀ k : ℕ, Measurable (σ k)) ∧
          (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
          (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
          ∃ Terminal : ℕ → Ω → ℝ≥0∞,
            ∃ error : ℕ → ℝ≥0∞,
              (∀ ε : ℝ≥0, 0 < ε →
                ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞)) ∧
              (∀ n k : ℕ,
                (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
                  ENNReal.ofReal (Real.exp (-(q * t)))
                    ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
                ≤ ENNReal.ofReal (w x) + error k)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal (∫ ω,
            (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hStrategy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        dividendValue X q x D ≤ ENNReal.ofReal (w x) ∧
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal (∫ ω,
            (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    intro x hx hxc D hD
    obtain ⟨σ, hm, hmono, hsup, Terminal, error, hError, hBudget⟩ :=
      hSource x hx hxc D hD
    exact avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
      X q x D hD.1 (ENNReal.ofReal (w x)) ENNReal.ofReal_lt_top
        σ hm hmono hsup Terminal error hError hBudget
  have hBounds := local_verification_from_uniform_strategy_bound
    X q w C (fun x hx hxc D hD => (hStrategy x hx hxc D hD).1)
  refine ⟨?_, hBounds.1, hBounds.2⟩
  intro x hx hxc D hD
  obtain ⟨hValue, hL1, hExact⟩ := hStrategy x hx hxc D hD
  refine ⟨hL1, hExact, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (hw x hx hxc)).mp
  simpa only [hExact] using hValue
