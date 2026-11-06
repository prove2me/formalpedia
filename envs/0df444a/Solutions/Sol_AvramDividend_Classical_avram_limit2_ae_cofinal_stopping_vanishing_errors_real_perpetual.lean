-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:11:10.56665+00:00
-- url     : https://prove2.me/submissions/fbd55535-3005-4a2e-adee-b69a0ccb4568

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Vanishing errors on cofinal clocks control original perpetual L1 cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hStopped : ∀ n k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
      ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  classical
  have hApprox (ε : ℝ≥0) (hε : 0 < ε) : dividendValue X q x D ≤ B + (ε : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hError ε hε
    let σN : ℕ → Ω → ℝ≥0∞ := fun k ω => σ (k + N) ω
    let TN : ℕ → Ω → ℝ≥0∞ := fun k ω => Terminal (k + N) ω
    have hm : ∀ k : ℕ, Measurable (σN k) := fun k => hσmeas (k + N)
    have hmono : ∀ ω : Ω, Monotone (fun k : ℕ => σN k ω) := by
      intro ω a b hab
      exact hσmono ω (Nat.add_le_add_right hab N)
    have hsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σN k ω) = ruinTime X x D ω := by
      filter_upwards [hSup] with ω hw
      change (⨆ k : ℕ, σ (k + N) ω) = ruinTime X x D ω
      calc
        (⨆ k : ℕ, σ (k + N) ω) = (⨆ k : ℕ, σ k ω) := by
          apply le_antisymm
          · exact iSup_le fun k => le_iSup (fun j : ℕ => σ j ω) (k + N)
          · exact iSup_le fun k =>
              (hσmono ω (Nat.le_add_right k N)).trans
                (le_iSup (fun j : ℕ => σ (j + N) ω) k)
        _ = ruinTime X x D ω := hw
    apply dividendValue_le_of_uniform_truncated_bounds X q x D hD (B + (ε : ℝ≥0∞))
    intro n
    apply avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
      X q x (n : ℝ) D hD.1 σN hm hmono hsup TN
        (B + (ε : ℝ≥0∞))
    intro k
    calc
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σN k ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + TN k ω) ∂P)
          ≤ B + error (k + N) := hStopped n (k + N)
      _ ≤ B + (ε : ℝ≥0∞) :=
        add_le_add_right (hN (k + N) (Nat.le_add_left N k)) B
  have hValue : dividendValue X q x D ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    exact hApprox ε hε
  have hFinite : dividendValue X q x D < ⊤ := lt_of_le_of_lt hValue hB
  obtain ⟨hL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  exact ⟨hValue, hL1, hExact⟩
