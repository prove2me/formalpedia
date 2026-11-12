-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b24_original_uniform_floor_A_integral_restrict_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:30:23.991332+00:00
-- url     : https://prove2.me/submissions/db96e01b-d5a5-4015-a43b-d1763a0fc61c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The genuine truncated uniform-floor A integrand has no mass outside the original horizon. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    (∫ t : ℝ, if 0 ≤ t ∧
        t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
          c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) =
    (∫ t in Icc 0 T, if 0 ≤ t ∧
        t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
          c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) := by
  let cutoff : ℝ := T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
  have hcut : cutoff ≤ T := by
    dsimp [cutoff]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
    nlinarith [hT.le]
  have hsupp (t : ℝ) (ht : t ∉ Icc (0 : ℝ) T) :
      ¬ (0 ≤ t ∧ t < cutoff) := by
    intro h
    exact ht ⟨h.1, le_trans h.2.le hcut⟩
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext t
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · simp [ht]
  · have hn : ¬ (0 ≤ t ∧
        t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
      simpa only [cutoff] using hsupp t ht
    simp [ht, hn]
