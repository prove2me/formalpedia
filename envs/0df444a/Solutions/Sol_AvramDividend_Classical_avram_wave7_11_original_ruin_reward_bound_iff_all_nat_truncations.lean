-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_ruin_reward_bound_iff_all_nat_truncations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:20:02.769802+00:00
-- url     : https://prove2.me/submissions/2e774ba7-b626-4979-9861-6a7147e7d1c7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A uniform bound on all genuine natural ruin truncations is equivalent
    to the complete original expected finite-horizon Stieltjes bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (b : ℝ≥0∞) :
    ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b) ↔
    (∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ b) := by
  rw [avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat
    X x D hD q T]
  exact iSup_le_iff
