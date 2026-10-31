-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:11.053986+00:00
-- url     : https://prove2.me/submissions/aab3889e-aae1-4551-8aaf-9cdcbf637f88

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- On an instant-ruin trajectory the entire capped original dividend reward
    is the time-zero payment, and admissibility bounds it by initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (T : ℝ≥0) (ω : Ω)
    (hruin : ruinTime X x D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal x := by
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hpay : paymentTimes (ruinTime X x D ω) = ({0} : Set ℝ) := by
    rw [hruin]
    simpa using paymentTimes_min_zero_eq_singleton_zero (0 : ℝ≥0∞)
  have hset : paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) =
      paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) := by
    rw [hpay]
    have hT : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
    have hleft : ({0} : Set ℝ) ⊆ Iic (T : ℝ) := by
      intro t ht
      simpa [Set.mem_singleton_iff.mp ht] using hT
    have hright : ({0} : Set ℝ) ⊆ Iic (0 : ℝ) := by
      intro t ht
      simp [Set.mem_singleton_iff.mp ht]
    rw [Set.inter_eq_left.mpr hleft, Set.inter_eq_left.mpr hright]
  have hcap := (capped_postPaymentReserve_initial_state X x C D hD hxc ω).1
  have hpayment : rightLimit D 0 ω - D 0 ω ≤ x := by
    simp only [X.X_zero ω, add_zero] at hcap
    rw [hs.1 ω]
    linarith
  calc
    _ = ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
      rw [hset]
      exact truncated_dividend_payoff_at_zero_eq_initial_atom D hs q
        (ruinTime X x D ω) ω
    _ ≤ ENNReal.ofReal x := ENNReal.ofReal_le_ofReal hpayment
