-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:56:42.255183+00:00
-- url     : https://prove2.me/submissions/af3697a5-b016-4e50-98cb-8017aa0b630b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The literal original terminal W is cap-bounded at every ruin/survival branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ENNReal.ofReal (W ω) ≤ C := by
  intro ω
  by_cases hpre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · have ht : τ ω = 0 ∨
        (0 < τ ω ∧ (τ ω : ℝ≥0∞) < ruinTime X x D ω) := by
      by_cases hz : τ ω = 0
      · exact Or.inl hz
      · exact Or.inr ⟨pos_iff_ne_zero.mpr hz, hpre.resolve_left hz⟩
    have hpart :=
      avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
        X x C D hD hxc ω (τ ω) ht
    rw [hW ω, if_pos hpre]
    rcases hpart with hz | heq | hinside
    · simp [hz]
    · exact le_of_eq heq
    · exact le_of_lt hinside.2
  · have hne : τ ω ≠ 0 := by
      intro hz
      exact hpre (Or.inl hz)
    rw [hW ω, if_neg hpre]
    exact hD.2 ω (τ ω) (pos_iff_ne_zero.mpr hne)
