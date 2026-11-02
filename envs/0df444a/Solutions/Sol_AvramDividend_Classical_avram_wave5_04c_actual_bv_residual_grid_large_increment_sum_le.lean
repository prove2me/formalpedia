-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:27:31.07984+00:00
-- url     : https://prove2.me/submissions/8a440e1a-ab80-406f-a1ed-5e7ab555ef2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal BigOperators
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (h : ℝ≥0) (n : ℕ) (M : ℝ) : ∀ᵐ ω ∂P, (∑ i ∈ Finset.range n, if M < ((↑((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift - X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) - (((i : ℝ≥0) * h : ℝ) * X.drift - X.X ((i : ℝ≥0) * h) ω) then ((↑((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift - X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) - (((i : ℝ≥0) * h : ℝ) * X.drift - X.X ((i : ℝ≥0) * h) ω) else 0) ≤ if M < (((n : ℝ≥0) * h : ℝ) * X.drift - X.X ((n : ℝ≥0) * h) ω) then (((n : ℝ≥0) * h : ℝ) * X.drift - X.X ((n : ℝ≥0) * h) ω) else 0 := by
  have aux (a : ℕ → ℝ) (hmono : Monotone a)
      (hzero : a 0 = 0) (n : ℕ) (M : ℝ) :
      (∑ i ∈ Finset.range n,
        if M < a (i + 1) - a i then a (i + 1) - a i else 0)
        ≤ if M < a n then a n else 0 := by
    have hnonneg (i : ℕ) : 0 ≤ a (i + 1) - a i :=
      sub_nonneg.mpr (hmono (Nat.le_succ i))
    have hsum : (∑ i ∈ Finset.range n, (a (i + 1) - a i)) = a n := by
      simpa [hzero] using (Finset.sum_range_sub a n)
    by_cases hn : M < a n
    · simp only [if_pos hn]
      calc
        (∑ i ∈ Finset.range n,
          if M < a (i + 1) - a i then a (i + 1) - a i else 0)
            ≤ ∑ i ∈ Finset.range n, (a (i + 1) - a i) := by
                apply Finset.sum_le_sum
                intro i hi
                split_ifs with hh
                · exact le_refl _
                · exact hnonneg i
        _ = a n := hsum
    · have hle (i : ℕ) (hi : i ∈ Finset.range n) :
          a (i + 1) - a i ≤ a n := by
        have hi1 : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
        have hai0 : 0 ≤ a i := by
          rw [← hzero]
          exact hmono (Nat.zero_le i)
        have haend : a (i + 1) ≤ a n := hmono hi1
        linarith
      have hnone (i : ℕ) (hi : i ∈ Finset.range n) :
          ¬ M < a (i + 1) - a i :=
        not_lt.mpr (le_trans (hle i hi) (le_of_not_gt hn))
      have hsum_zero :
          (∑ i ∈ Finset.range n,
            if M < a (i + 1) - a i then a (i + 1) - a i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [hnone i hi]
      simp [hn, hsum_zero]
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hmono
  let a : ℕ → ℝ := fun i =>
    (((i : ℝ≥0) * h : ℝ) * X.drift - X.X ((i : ℝ≥0) * h) ω)
  have ha : Monotone a := by
    intro i j hij
    change
      (((i : ℝ≥0) * h : ℝ) * X.drift - X.X ((i : ℝ≥0) * h) ω) ≤
      (((j : ℝ≥0) * h : ℝ) * X.drift - X.X ((j : ℝ≥0) * h) ω)
    exact hmono (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity))
  have ha0 : a 0 = 0 := by
    simp [a, X.X_zero]
  exact aux a ha ha0 n M