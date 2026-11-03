-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:08:26.715878+00:00
-- url     : https://prove2.me/submissions/e5ae5c50-6298-42cf-bebc-b23493c5834c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
/-- Exact original paid horizon singleton and HJB value drop, including zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0)
    (hactive : S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω) (q : ℝ) :
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
        ({(S : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (S : ℝ))) *
        w (riskProcess X x D S ω - (rightLimit D S ω - D S ω)) ≤
      Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) := by
  classical
  have hΔ : 0 ≤ rightLimit D S ω - D S ω := sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω S)
  have he : 0 ≤ Real.exp (-(q * (S : ℝ))) := le_of_lt (Real.exp_pos _)
  have hmem : (S : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by
    change 0 ≤ (S : ℝ) ∧
      ((S : ℝ) = 0 ∨ ENNReal.ofReal (S : ℝ) < ruinTime X x D ω)
    refine ⟨S.property, ?_⟩
    rcases hactive with hz | ht
    · exact Or.inl (by exact_mod_cast hz)
    · exact Or.inr (by simpa using ht)
  have hset : (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
      ({(S : ℝ)} : Set ℝ) = paymentTimes (ruinTime X x D ω) ∩ ({(S : ℝ)} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · rintro ⟨hp, rfl⟩
      exact ⟨⟨hp, Set.mem_Iic.mpr (le_refl _)⟩, rfl⟩
  have hlin :
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        ENNReal.ofReal (Real.exp (-(q * (S : ℝ)))) *
          ENNReal.ofReal (rightLimit D S ω - D S ω) := by
    rw [hset]
    rw [paymentTimes_terminal_active_lintegral_eq_atom
      (dividendMeasure D ω) (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
      (ruinTime X x D ω) (S : ℝ) hmem]
    rw [dividendMeasure_singleton_eq_rightLimit_sub D hD ω S]
  have hcash :
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
        Real.exp (-(q * (S : ℝ))) * (rightLimit D S ω - D S ω) := by
    rw [hlin, ENNReal.toReal_mul, ENNReal.toReal_ofReal he,
      ENNReal.toReal_ofReal hΔ]
  have hdrop :
      (rightLimit D S ω - D S ω) +
        w (riskProcess X x D S ω - (rightLimit D S ω - D S ω)) ≤
          w (riskProcess X x D S ω) := by
    linarith [hjump ω S hactive]
  calc
    _ = Real.exp (-(q * (S : ℝ))) *
          ((rightLimit D S ω - D S ω) +
            w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))) := by
          rw [hcash]
          ring
    _ ≤ Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) :=
      mul_le_mul_of_nonneg_left hdrop he
