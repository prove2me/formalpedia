-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_countable_uniform_interior_cutoff_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:17:41.740542+00:00
-- url     : https://prove2.me/submissions/c407fec8-c9bd-4157-80f4-c2ee8e5b3abe

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
Countably many strictly interior slope-one cutoffs approximate the
true cap continuation uniformly over all nonnegative reserves at
specified vanishing error tolerances. Every kink stays within C2.
-/

/-- A countable sequence of interior cutoffs is uniformly accurate
    at all reserve states, without imposing any cap endpoint derivative. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c) ∧
      ∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1) := by
  classical
  have hExist (n : ℕ) :
      ∃ b : ℝ, 0 < b ∧ b < c ∧
        ∀ y : ℝ, 0 ≤ y →
          0 ≤ (if y ≤ c then w y else w c + (y - c)) -
            (if y ≤ b then w y else w b + (y - b)) ∧
          (if y ≤ c then w y else w c + (y - c)) -
            (if y ≤ b then w y else w b + (y - b)) <
            1 / ((n : ℝ) + 1) :=
    avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_approximation
      w c hc hw_cont hw_smooth hw_grad
      (1 / ((n : ℝ) + 1)) (by positivity)
  let b : ℕ → ℝ := fun n => Classical.choose (hExist n)
  have hSpec (n : ℕ) := Classical.choose_spec (hExist n)
  refine ⟨b, ?_, ?_⟩
  · intro n
    exact ⟨(hSpec n).1, (hSpec n).2.1⟩
  · intro n y hy
    exact (hSpec n).2.2 y hy
