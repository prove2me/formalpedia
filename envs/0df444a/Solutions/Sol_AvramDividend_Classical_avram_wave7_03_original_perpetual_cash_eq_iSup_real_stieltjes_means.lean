-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:20:15.08353+00:00
-- url     : https://prove2.me/submissions/46fec1d5-b687-4f61-a8f1-d7847611ebe2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original perpetual payout is the supremum of exact finite-horizon
    signed real Stieltjes expectations on the original stopped sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hFm (n : ℕ) : Measurable (F n) := by
    simpa only [F] using
      (avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
        X x D hDiv q (fun _ => (((n + 1 : ℕ) : ℝ))) measurable_const)
  have hFmono : Monotone F := by
    intro n m hnm ω
    apply MeasureTheory.lintegral_mono_set
    intro t ht
    have hnmReal : (((n + 1 : ℕ) : ℝ)) ≤ (((m + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact ⟨ht.1, (Set.mem_Iic.mp ht.2).trans hnmReal⟩
  have hPoint (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, F n ω := by
    simpa only [F] using
      (avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
        X x D hDiv q ω)
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ⨆ n, F n ω ∂P) := by
        apply lintegral_congr
        intro ω
        exact hPoint ω
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := lintegral_iSup hFm hFmono
    _ = ⨆ n : ℕ, ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (((n + 1 : ℕ) : ℝ)),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
        apply iSup_congr
        intro n
        simpa only [F, NNReal.coe_natCast] using
          (avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
            X x C D hD q hq (((n + 1 : ℕ) : ℝ≥0)))
