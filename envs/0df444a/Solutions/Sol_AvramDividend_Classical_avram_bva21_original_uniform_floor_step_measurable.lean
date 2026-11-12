-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_original_uniform_floor_step_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:15:02.312326+00:00
-- url     : https://prove2.me/submissions/2b2bb2fa-5f65-452f-a034-d45b05154739

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- The actual inclusive-floor Riemann compensator integrand is measurable. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    Measurable (fun t : ℝ =>
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) := by
  classical
  let u : ℕ → ℝ := fun i => T * (i : ℝ) / ((n : ℝ) + 2)
  have hsum : Measurable (fun t : ℝ =>
      ∑ i ∈ Finset.range (n + 1),
        (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) := by
    measurability
  have hEq :
      (fun t : ℝ =>
        if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
        then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) =
      (fun t : ℝ =>
        ∑ i ∈ Finset.range (n + 1),
          (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) := by
    funext t
    simpa only [u] using
      (avram_bva20_uniform_step_full_floor_mask_identity T hT n c t).symm
  rw [hEq]
  exact hsum
