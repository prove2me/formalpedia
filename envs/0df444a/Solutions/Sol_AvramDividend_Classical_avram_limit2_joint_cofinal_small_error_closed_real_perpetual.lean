-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_joint_cofinal_small_error_closed_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:12:22.241615+00:00
-- url     : https://prove2.me/submissions/db505634-2c23-46ff-8542-69b6e25e71f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Original closed cash is bounded whenever every horizon admits one
    sufficiently far horizon with an arbitrarily small error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (error : ℕ → ℝ≥0∞)
    (hGood : ∀ ε : ℝ≥0, 0 < ε → ∀ a : ℝ,
      ∃ k : ℕ, a ≤ T k ∧ error k ≤ (ε : ℝ≥0∞))
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  classical
  let cash : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  have hEach (n : ℕ) : cash n ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨k, hTk, hkErr⟩ := hGood ε hε (n : ℝ)
    obtain ⟨Terminal, hTerminal⟩ := hBudget k
    calc
      cash n ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
          dsimp [cash]
          apply lintegral_mono
          intro ω
          apply lintegral_mono_set
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hTk⟩
      _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
          apply lintegral_mono
          intro ω
          exact le_add_of_nonneg_right bot_le
      _ ≤ B + error k := hTerminal
      _ ≤ B + (ε : ℝ≥0∞) := add_le_add_right hkErr B
  have hValue : dividendValue X q x D ≤ B := by
    rw [dividendValue_eq_iSup_truncated X q x D hD]
    change (⨆ n : ℕ, cash n) ≤ B
    exact iSup_le hEach
  have hFinite : dividendValue X q x D < ⊤ := lt_of_le_of_lt hValue hB
  obtain ⟨hL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  exact ⟨hValue, hL1, hExact⟩
