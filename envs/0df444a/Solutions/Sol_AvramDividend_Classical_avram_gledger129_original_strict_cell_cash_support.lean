-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger129_original_strict_cell_cash_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:40:45.818211+00:00
-- url     : https://prove2.me/submissions/b10079a8-5fa4-4909-b2aa-1f8ad01a7548

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger101_original_strict_clipped_clock_payment_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (v : ℕ → ℝ≥0) (i : ℕ) (hi : v (i + 1) < ρ) :
    (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc (v i : ℝ) (v (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal := by
  have hsubset : Ioc (v i : ℝ) (v (i + 1) : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) := by
    intro s hs
    have hspos : 0 < s := lt_of_le_of_lt (v i).property hs.1
    have hslt : s < (ρ : ℝ) := lt_of_le_of_lt hs.2 (by exact_mod_cast hi)
    exact (avram_gledger101_original_strict_clipped_clock_payment_support
      (ruinTime X x D ω) ρ hρ ⟨hspos, hslt⟩).1
  have hset : paymentTimes (ruinTime X x D ω) ∩
      Ioc (v i : ℝ) (v (i + 1) : ℝ) =
      Ioc (v i : ℝ) (v (i + 1) : ℝ) :=
    Set.inter_eq_right.mpr hsubset
  rw [hset]
