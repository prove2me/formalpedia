-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_zero_clock_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:43:39.121014+00:00
-- url     : https://prove2.me/submissions/ee273b2f-4a22-45ce-b5c0-ac4b1b5df28e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q T : ℝ) (hT : 0 < T) :
    (∫⁻ t in paymentTimes 0 ∩ Iio T, ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal ≤ rightLimit D 0 ω := by
  have hset : paymentTimes 0 ∩ Iio T = ({0} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      rcases ht.1.2 with hz | hn
      · exact hz
      · exact False.elim ((not_lt_of_ge zero_le) hn)
    · intro ht
      subst t
      exact ⟨⟨le_rfl, Or.inl rfl⟩, hT⟩
  haveI : Nonempty (Ioi (0 : ℝ≥0)) := ⟨⟨1, by norm_num⟩⟩
  have hr : 0 ≤ rightLimit D 0 ω := by
    apply le_ciInf
    intro s
    have h := hD.2.1 ω (show 0 ≤ s.val from zero_le)
    simpa only [hD.1 ω] using h
  have hm : dividendMeasure D ω {(0 : ℝ)} = ENNReal.ofReal (rightLimit D 0 ω) := by
    simpa only [NNReal.coe_zero, hD.1 ω, sub_zero] using
      dividendMeasure_singleton_eq_rightLimit_sub D hD ω 0
  rw [hset, lintegral_singleton]
  simp only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, hm]
  exact le_of_eq (ENNReal.toReal_ofReal hr)
end
