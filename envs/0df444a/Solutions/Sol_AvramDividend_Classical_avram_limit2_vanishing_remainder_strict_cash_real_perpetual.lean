-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_vanishing_remainder_strict_cash_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:12:38.843784+00:00
-- url     : https://prove2.me/submissions/d140fee0-e178-4e91-aa33-de39994fe26a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_integer_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Strict cash budgets with vanishing error bound perpetual real payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → error n ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error n) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  classical
  let cash : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iio (((n + 1 : ℕ) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  have hMono : Monotone cash := by
    intro m n hmn
    dsimp [cash]
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    have hmnR : (((m + 1 : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) := by exact_mod_cast (Nat.add_le_add_right hmn 1)
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hmnR⟩
  have hCash (n : ℕ) : cash n ≤ B + error n := by
    obtain ⟨Terminal, hTerminal⟩ := hBudget n
    dsimp [cash]
    calc
      _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
          apply lintegral_mono
          intro ω
          exact le_add_of_nonneg_right bot_le
      _ ≤ B + error n := hTerminal
  have hEach (n : ℕ) : cash n ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨N, hN⟩ := hError ε hε
    let k := max n N
    have hnk : n ≤ k := le_max_left n N
    have hNk : N ≤ k := le_max_right n N
    calc
      cash n ≤ cash k := hMono hnk
      _ ≤ B + error k := hCash k
      _ ≤ B + (ε : ℝ≥0∞) := add_le_add_right (hN k hNk) B
  have hValue : dividendValue X q x D ≤ B := by
    rw [avram_limit2_original_strict_positive_integer_horizon_exhaustion X q x D hD]
    change (⨆ n : ℕ, cash n) ≤ B
    exact iSup_le hEach
  have hFinite : dividendValue X q x D < ⊤ := lt_of_le_of_lt hValue hB
  obtain ⟨hL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  exact ⟨hValue, hL1, hExact⟩
