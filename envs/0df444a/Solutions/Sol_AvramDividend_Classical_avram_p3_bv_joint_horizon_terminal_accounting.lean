-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_joint_horizon_terminal_accounting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:02:30.220818+00:00
-- url     : https://prove2.me/submissions/840374d0-5e2a-49f6-aa9c-c47e52ecceca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_survival_horizon_atom_absorption
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_nonsurvival_horizon_cash_open
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original stopped cash and the exact strict-survival postpayment terminal
    reduce to pre-horizon cash and the prepayment terminal in both branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
        else 0) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) := by
  let S : ℝ≥0 := ⟨T, hT⟩
  have hsurvive := avram_p3_bv_survival_horizon_atom_absorption
    X x C D hD q w hjump T hT
  have hnonsurvive := avram_p3_bv_nonsurvival_horizon_cash_open
    X x C D hD q T hT hTpos
  filter_upwards [hsurvive, hnonsurvive] with ω hs hn
  split_ifs with hactive
  · exact hs hactive
  · simpa only [add_zero] using (le_of_eq (hn hactive))
