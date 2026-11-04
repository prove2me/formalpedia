-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:32:47.275395+00:00
-- url     : https://prove2.me/submissions/28b03da2-28c1-441c-a990-a3eb30c55354

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Each genuinely paid nonzero Cash atom has the physical HJB clock and right-jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ u : ℝ≥0, u ≤ T →
      μatom {(u : ℝ)} = ENNReal.ofReal (rightLimit D u ω - D u ω)) :
    ∀ a : {t : ℝ | t ∈ A ∧ t ∈ paymentTimes (ruinTime X x D ω) ∧
      μatom {t} ≠ 0},
      0 ≤ a.1 ∧ Real.toNNReal a.1 ≤ T ∧
      (Real.toNNReal a.1 = 0 ∨
        (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω) ∧
      0 ≤ rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω ∧
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω) ∧
      rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω ≤
        w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω)) := by
  intro a
  obtain ⟨h0, hT, hm⟩ :=
    (avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
      D ω T μatom μdiffuse hsplit hRight A)
      ⟨a.1, a.2.1, a.2.2.2⟩
  have helig : Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω := by
    rcases avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
      X x D ω a.1 a.2.2.1 with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hdelta : 0 ≤ rightLimit D (Real.toNNReal a.1) ω -
      D (Real.toNNReal a.1) ω := by
    by_contra h
    have hz : ENNReal.ofReal (rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω) = 0 :=
      ENNReal.ofReal_of_nonpos (le_of_not_ge h)
    exact a.2.2.2 (hm.trans hz)
  exact ⟨h0, hT, helig, hdelta, hm,
    hjump ω (Real.toNNReal a.1) helig⟩
