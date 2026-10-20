-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_dividend_payoff_zero_at_immediate_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:31:04.940521+00:00
-- url     : https://prove2.me/submissions/545f7404-0cb6-4d48-b346-5ce169063dba

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_zero_cap_rightLimit_zero_at_origin
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (hσ : ruinTime X 0 D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X 0 D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
  have hpay : paymentTimes (ruinTime X 0 D ω) = {(0 : ℝ)} := by
    ext t
    simp only [paymentTimes, hσ, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨htnonneg, htzero | htneg⟩
      · exact htzero
      · exact (not_lt_of_ge
          (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal t from zero_le) htneg).elim
    · intro htzero
      subst t
      exact ⟨le_refl _, Or.inl rfl⟩
  have hmass : dividendMeasure D ω {(0 : ℝ)} = 0 := by
    have hmass0 : dividendMeasure D ω {(0 : ℝ)} =
        ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
      simpa using (dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω (0 : ℝ≥0))
    rw [hmass0]
    simp [zero_cap_rightLimit_zero_at_origin X D hD ω, hD.1.1.1 ω]
  rw [hpay]
  exact setLIntegral_measure_zero _ _ hmass
