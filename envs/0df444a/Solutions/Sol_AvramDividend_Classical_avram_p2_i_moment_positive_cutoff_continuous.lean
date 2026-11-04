-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_positive_cutoff_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:44:54.234021+00:00
-- url     : https://prove2.me/submissions/e2044aef-2cee-43b7-9655-d0a3b8e36945

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set

/-- A continuous linear ramp suppresses negative arguments without changing positive tests. -/
theorem solution
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    ∃ u : ℝ → ℝ,
      Continuous u ∧
      (∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → u z = 0) ∧
      (∀ z : ℝ, 0 ≤ z → u z = g z) := by
  refine ⟨(fun z : ℝ => min 1 (max 0 (z / δ)) * g z), ?_, ?_, ?_⟩
  · fun_prop
  · intro z hz
    rcases hz with hz | hz
    · have hd : z / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz hδ.le
      simp [max_eq_left hd]
    · simp [hzero_upper z hz]
  · intro z hz
    by_cases hsmall : z ≤ δ
    · simp [hzero_small z hz hsmall]
    · have hlarge : δ < z := lt_of_not_ge hsmall
      have hdiv : (1 : ℝ) ≤ z / δ := by
        apply (le_div_iff₀ hδ).2
        nlinarith
      have hmax : max 0 (z / δ) = z / δ :=
        max_eq_right (le_trans (by norm_num) hdiv)
      have hmin : min (1 : ℝ) (z / δ) = 1 := min_eq_left hdiv
      simp [hmax, hmin]
