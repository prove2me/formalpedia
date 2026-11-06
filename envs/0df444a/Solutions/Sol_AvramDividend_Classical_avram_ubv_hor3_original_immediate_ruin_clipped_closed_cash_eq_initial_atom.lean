-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_clipped_closed_cash_eq_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:10:52.129906+00:00
-- url     : https://prove2.me/submissions/a78b0a1f-05e6-4918-9d65-c60d082d37aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) (ω : Ω)
    (hRuinZero : ruinTime X x D ω = 0) :
    (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (dividendMeasure D ω) ({0} : Set ℝ) := by
  have hClippedZero :
      min (ruinTime X x D ω) (n : ℝ≥0∞) = 0 := by
    simp [hRuinZero]
  have hDomain :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T =
        paymentTimes (0 : ℝ≥0∞) ∩ Iic (0 : ℝ) := by
    rw [hClippedZero]
    ext s
    constructor
    · intro hs
      have hsZero : s = 0 := by
        rcases hs.1 with ⟨_, hcases⟩
        rcases hcases with hz | hlt
        · exact hz
        · exact False.elim ((not_lt_of_ge bot_le) hlt)
      subst s
      simp [paymentTimes]
    · intro hs
      exact ⟨hs.1, hs.2.trans hT⟩
  rw [hDomain]
  exact avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
    D ω 0 q
