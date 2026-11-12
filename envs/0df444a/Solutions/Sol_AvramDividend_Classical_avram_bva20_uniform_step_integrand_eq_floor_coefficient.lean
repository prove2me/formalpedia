-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_uniform_step_integrand_eq_floor_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:38:55.702179+00:00
-- url     : https://prove2.me/submissions/b9b9848b-fa5f-4a45-bdc6-ae2286381552

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_floor_index_within_inner_row
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_floor_sample_mem_halfopen_cell
import Theorems.Thm_AvramDividend_Classical_avram_bva20_halfopen_monotone_grid_step_select

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- The occupied original physical uniform cell selects its frozen coefficient. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t)
    (htInner : t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)) :
    let u : ℕ → ℝ := fun i => T * (i : ℝ) / ((n : ℝ) + 2)
    (∑ i ∈ Finset.range (n + 1),
      (Set.Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
      c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ := by
  intro u
  let k : ℕ := ⌊(t / T) * ((n : ℝ) + 2)⌋₊
  have hk : k < n + 1 :=
    avram_bva20_uniform_floor_index_within_inner_row T hT n t ht0 htInner
  have hmem : t ∈ Ico (u k) (u (k + 1)) := by
    have hcell := avram_bva20_uniform_floor_sample_mem_halfopen_cell
      T hT t ht0 n
    simpa only [u, k, Nat.cast_add, Nat.cast_one] using hcell
  have hu : StrictMono u := by
    intro a b hab
    dsimp [u]
    apply div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left (by exact_mod_cast hab) hT)
      (by positivity)
  exact avram_bva20_halfopen_monotone_grid_step_select
    n k hk u hu c t hmem
