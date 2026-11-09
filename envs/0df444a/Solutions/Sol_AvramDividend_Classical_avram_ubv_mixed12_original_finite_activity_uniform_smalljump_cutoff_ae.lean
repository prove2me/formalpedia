-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T20:20:51.482737+00:00
-- url     : https://prove2.me/submissions/a2fbd123-fa94-4ade-b761-ed315f8e7744

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- All actual original small jumps disappear beyond one cutoff, uniformly on a bounded clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| ≤
          1 / ((n : ℝ) + 1) →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  classical
  have hAll := avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae X hFinite
  filter_upwards [hAll] with ω hω
  intro T
  obtain ⟨ε, hε, hGap⟩ := hω T
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn u hu0 huT hsmall
  by_contra hj
  have hlarge := hGap u hu0 huT hj
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNprod : 1 < ε * (N : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith [h]
  have hden : 0 < ((n : ℝ) + 1) := by positivity
  have hprod : 1 < ε * ((n : ℝ) + 1) := by
    have hmono : ε * (N : ℝ) ≤ ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hnreal (le_of_lt hε)
    nlinarith
  have hcutoff : (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    (div_lt_iff₀ hden).mpr (by nlinarith)
  linarith
