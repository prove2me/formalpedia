-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_uniform_step_full_floor_mask_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:46:00.389456+00:00
-- url     : https://prove2.me/submissions/1942b4da-23f6-4600-97a3-c2fffd4c4c7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_integrand_eq_floor_coefficient
import Theorems.Thm_AvramDividend_Classical_avram_bva20_monotone_grid_step_zero_outside_row

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- The full frozen physical-grid step integrand is its masked floor coefficient. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    let u : ℕ → ℝ := fun i => T * (i : ℝ) / ((n : ℝ) + 2)
    (∑ i ∈ Finset.range (n + 1),
      (Set.Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
    if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
      c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by
  intro u
  have hu : StrictMono u := by
    intro i j hij
    dsimp [u]
    apply div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left (by exact_mod_cast hij) hT)
      (by positivity)
  by_cases h : 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
  · simpa only [if_pos h] using
      (avram_bva20_uniform_step_integrand_eq_floor_coefficient
        T hT n c t h.1 h.2)
  · have hnot : t ∉ Ico (u 0) (u (n + 1)) := by
      intro ht
      apply h
      simpa [u] using ht
    have hs := avram_bva20_monotone_grid_step_zero_outside_row
      n u hu c t hnot
    simpa only [if_neg h] using hs
