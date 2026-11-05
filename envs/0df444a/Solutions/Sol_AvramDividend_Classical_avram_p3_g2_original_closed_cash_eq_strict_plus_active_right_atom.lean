-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:37:15.310736+00:00
-- url     : https://prove2.me/submissions/34993a0a-f751-43e6-a2ef-73a8ab5830aa

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Full literal stopped cash has exactly one extra right-horizon atom.
The atom survives at zero and at strict pre-ruin horizons, but vanishes
when ruin occurs at or before the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * (rightLimit D S ω - D S ω)
      else 0) := by
  classical
  rw [avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
    X x C D hD ω q hq S]
  congr 1
  by_cases hactive : S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω
  · rw [if_pos hactive]
    have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
    have hΔ : 0 ≤ rightLimit D S ω - D S ω :=
      sub_nonneg.mpr (dividendStrategy_le_rightLimit D hDstrat ω S)
    have he : 0 ≤ Real.exp (-(q * (S : ℝ))) := (Real.exp_pos _).le
    have hmem : (S : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by
      change 0 ≤ (S : ℝ) ∧
        ((S : ℝ) = 0 ∨ ENNReal.ofReal (S : ℝ) < ruinTime X x D ω)
      refine ⟨S.property, ?_⟩
      rcases hactive with hz | ht
      · exact Or.inl (by exact_mod_cast hz)
      · exact Or.inr (by simpa using ht)
    have hset :
        (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ) =
        paymentTimes (ruinTime X x D ω) ∩
          ({(S : ℝ)} : Set ℝ) := by
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
        (dividendMeasure D ω)
        (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
        (ruinTime X x D ω) (S : ℝ) hmem]
      rw [dividendMeasure_singleton_eq_rightLimit_sub D hDstrat ω S]
    rw [hlin, ENNReal.toReal_mul, ENNReal.toReal_ofReal he,
      ENNReal.toReal_ofReal hΔ]
  · rw [if_neg hactive]
    have hnotmem : (S : ℝ) ∉ paymentTimes (ruinTime X x D ω) := by
      intro hm
      change 0 ≤ (S : ℝ) ∧
        ((S : ℝ) = 0 ∨ ENNReal.ofReal (S : ℝ) < ruinTime X x D ω) at hm
      apply hactive
      rcases hm.2 with hz | ht
      · exact Or.inl (by exact_mod_cast hz)
      · exact Or.inr (by simpa using ht)
    have hset :
        (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ) = ∅ := by
      ext t
      constructor
      · intro ht
        have hs : t = (S : ℝ) := ht.2
        subst t
        exact (hnotmem ht.1.1).elim
      · simp
    simp [hset]
