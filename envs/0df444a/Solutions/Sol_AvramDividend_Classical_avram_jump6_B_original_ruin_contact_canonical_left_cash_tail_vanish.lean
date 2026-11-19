-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_ruin_contact_canonical_left_cash_tail_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:04:29.417212+00:00
-- url     : https://prove2.me/submissions/e7083737-3e39-45f4-a80a-a77b2d5902e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hContact : (t : ℝ≥0∞) = ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun j : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((t : ℝ) - (1 / ((j : ℝ) + 1))) (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hPos : ∀ j, 0 < δ j := by intro j; dsimp [δ]; positivity
  have hAnti : Antitone δ := by
    apply antitone_nat_of_succ_le
    intro j
    dsimp [δ]
    gcongr
    omega
  have hZero : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
    simpa only [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
    X x D hD ω t ht hContact q hq δ hPos hAnti hZero
