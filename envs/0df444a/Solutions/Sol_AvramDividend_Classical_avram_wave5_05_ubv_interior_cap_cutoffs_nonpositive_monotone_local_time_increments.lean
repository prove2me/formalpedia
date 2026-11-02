-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_interior_cap_cutoffs_nonpositive_monotone_local_time_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:55:40.804913+00:00
-- url     : https://prove2.me/submissions/b44f79a0-3e62-4dab-9630-d9143fabac1c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
For any monotone real increasing local-time clock, the
finite Itô–Tanaka kink coefficient at every strictly
interior cap cutoff contributes nonpositively on
every stopping interval, including one beginning at zero.
No stochastic chain rule is asserted.
-/

theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c ∧
        c - b n < 1 / ((n : ℝ) + 1)) ∧
      (∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1)) ∧
      ∀ (n : ℕ) (L : ℝ≥0 → ℝ), Monotone L →
        ∀ (s t : ℝ≥0), s ≤ t →
          (1 - deriv w (b n)) * (L t - L s) ≤ 0 := by
  obtain ⟨b, hLoc, hKink, hUniform⟩ :=
    avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks
      w c hc hw_cont hw_smooth hw_grad
  refine ⟨b, hLoc, hUniform, ?_⟩
  intro n L hMono s t hst
  have hClock : 0 ≤ L t - L s :=
    sub_nonneg.mpr (hMono hst)
  exact mul_nonpos_of_nonpos_of_nonneg (hKink n).2.2 hClock
