-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:09:34.156293+00:00
-- url     : https://prove2.me/submissions/0d655b90-dce5-4eb2-95aa-e4d60a68ff3e

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
/-- Diagonal cofinal stopped cash bounds actual original perpetual payout. -/
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
    (hError : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hDiagonal : ∀ k : ℕ, (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (k : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
          Terminal k ω) ∂P) ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω => ∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D = ENNReal.ofReal (∫ ω,
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  classical
  have hApprox (ε : ℝ≥0) (hε : 0 < ε) : dividendValue X q x D ≤ B + (ε : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hError ε hε
    apply dividendValue_le_of_uniform_truncated_bounds X q x D hD (B + (ε : ℝ≥0∞))
    intro n
    let K := max n N
    let σK : ℕ → Ω → ℝ≥0∞ := fun k ω => σ (k + K) ω
    let TK : ℕ → Ω → ℝ≥0∞ := fun k ω => Terminal (k + K) ω
    have hm : ∀ k : ℕ, Measurable (σK k) := fun k => hσmeas (k + K)
    have hmono : ∀ ω : Ω, Monotone (fun k : ℕ => σK k ω) := by
      intro ω a b hab; exact hσmono ω (Nat.add_le_add_right hab K)
    have hsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σK k ω) = ruinTime X x D ω := by
      filter_upwards [hSup] with ω hw
      change (⨆ k : ℕ, σ (k + K) ω) = ruinTime X x D ω
      calc
        (⨆ k : ℕ, σ (k + K) ω) = (⨆ k : ℕ, σ k ω) := by
          apply le_antisymm
          · exact iSup_le fun k => le_iSup (fun j : ℕ => σ j ω) (k + K)
          · exact iSup_le fun k =>
              (hσmono ω (Nat.le_add_right k K)).trans (le_iSup (fun j : ℕ => σ (j + K) ω) k)
        _ = ruinTime X x D ω := hw
    apply avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
      X q x (n : ℝ) D hD.1 σK hm hmono hsup TK (B + (ε : ℝ≥0∞))
    intro k
    have hnNat : n ≤ k + K := le_trans (le_max_left n N) (Nat.le_add_left K k)
    have hnReal : (n : ℝ) ≤ ((k + K : ℕ) : ℝ) := by exact_mod_cast hnNat
    have hNK : N ≤ k + K := le_trans (le_max_right n N) (Nat.le_add_left K k)
    calc
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σK k ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + TK k ω) ∂P) ≤
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ (k + K) ω) ∩ Iic ((k + K : ℕ) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + Terminal (k + K) ω) ∂P) := by
          apply lintegral_mono
          intro ω
          dsimp only [σK, TK]
          apply add_le_add_left
          apply lintegral_mono_set
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hnReal⟩
      _ ≤ B + error (k + K) := hDiagonal (k + K)
      _ ≤ B + (ε : ℝ≥0∞) := add_le_add_right (hN (k + K) hNK) B
  have hValue : dividendValue X q x D ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _; exact hApprox ε hε
  have hFinite : dividendValue X q x D < ⊤ := lt_of_le_of_lt hValue hB
  obtain ⟨hL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite X x D hD.1 q hFinite
  exact ⟨hValue, hL1, hExact⟩
