-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_uniform_physical_cell_size_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:27:02.394464+00:00
-- url     : https://prove2.me/submissions/b045a58f-6482-4d86-8db8-a7fa65f72bec

import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open Filter
open scoped NNReal
noncomputable section

theorem solution
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ((T / ((m + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hNm1 : (N : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hbig' : (T : ℝ) < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hN
  have hbig : (T : ℝ) < δ * (N : ℝ) := by
    simpa only [mul_comm] using hbig'
  have hmul : δ * (N : ℝ) ≤ δ * ((m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hNm1 (le_of_lt hδ)
  have hfrac : (T : ℝ) / ((m : ℝ) + 1) < δ :=
    (div_lt_iff₀ hden).mpr (lt_of_lt_of_le hbig hmul)
  simpa [NNReal.coe_div, Nat.cast_add] using hfrac
