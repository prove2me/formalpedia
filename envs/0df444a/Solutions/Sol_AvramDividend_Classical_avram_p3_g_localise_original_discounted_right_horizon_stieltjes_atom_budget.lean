-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_discounted_right_horizon_stieltjes_atom_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:53:58.172203+00:00
-- url     : https://prove2.me/submissions/e52f1c94-0b9e-49e6-8c59-ac4d8a417f06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original Stieltjes singleton at the zero or strict pre-ruin
right horizon pays its jump and preserves the HJB terminal drop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (S : ℝ≥0),
      (S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω) →
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω) ≤
      Real.exp (-(q * (S : ℝ))) *
        w (riskProcess X x D S ω) := by
  classical
  intro ω S hactive
  have hΔ : 0 ≤ rightLimit D S ω - D S ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω S)
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
    rw [dividendMeasure_singleton_eq_rightLimit_sub D hD ω S]
  have hcash :
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
        Real.exp (-(q * (S : ℝ))) *
          (rightLimit D S ω - D S ω) := by
    rw [hlin, ENNReal.toReal_mul, ENNReal.toReal_ofReal he,
      ENNReal.toReal_ofReal hΔ]
  rw [hcash]
  exact
    avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
      X x D w q hjump ω S hactive
