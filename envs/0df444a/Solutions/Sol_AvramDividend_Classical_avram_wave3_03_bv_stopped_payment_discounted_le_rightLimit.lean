-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:32:57.608328+00:00
-- url     : https://prove2.me/submissions/88a920a0-1cc1-498e-87d0-b38739891ebb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The actual finite-horizon stopped dividend-payment Stieltjes integral,
including continuous and singular-continuous mass, is bounded by the total
right-limit cumulative dividends, including the terminal right payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D T ω) := by
  have hsubset : paymentTimes σ ∩ Iic (T : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, ht.2⟩
  calc
    _ ≤ (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
        lintegral_mono_set hsubset
    _ ≤ _ := avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
      q hq D hD ω T
