-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_smalljump_tsum_eventually_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T21:44:22.484917+00:00
-- url     : https://prove2.me/submissions/18c90c5f-ce9e-472e-917f-1fae52011d66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual finite-activity jump-source series vanishes uniformly beyond a
    pathwise cutoff on every bounded physical horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ T ∧
            |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| ≤
              1 / ((k : ℝ) + 1) then
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0) = 0 := by
  classical
  have hGap :=
    avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
      X hFinite
  filter_upwards [hGap] with ω hω
  intro T
  obtain ⟨N, hN⟩ := hω T
  refine ⟨N, ?_⟩
  intro k hk
  have hterms :
      (fun u : ℝ≥0 =>
        if 0 < u ∧ u ≤ T ∧
            |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| ≤
              1 / ((k : ℝ) + 1) then
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0) = (fun _ => (0 : ℝ)) := by
    funext u
    split_ifs with hu
    · exact hN k hk u hu.1 hu.2.1 hu.2.2
    · rfl
  rw [hterms]
  simp
