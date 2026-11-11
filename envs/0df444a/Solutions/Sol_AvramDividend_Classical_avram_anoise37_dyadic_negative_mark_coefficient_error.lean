-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise37_dyadic_negative_mark_coefficient_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:25:07.662012+00:00
-- url     : https://prove2.me/submissions/89ea94a0-b60f-44e0-a08f-8e3c432970bb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Dyadic signed left-endpoint marks have at most one cell of error and unit size. -/
theorem solution
    (k i : ℕ) (z : ℝ)
    (hi : i < 2 ^ k)
    (hz : z ∈ Set.Ioc
      (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)) :
    |(-1 + (i : ℝ) / (2 : ℝ) ^ k) - z| ≤
      1 / (2 : ℝ) ^ k ∧
    |(-1 + (i : ℝ) / (2 : ℝ) ^ k)| ≤ 1 := by
  rcases hz with ⟨hlo, hhi⟩
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  have hip : (i : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast hi
  have hq : (i : ℝ) / (2 : ℝ) ^ k < 1 := by
    apply (div_lt_iff₀ hp).2
    simpa only [one_mul] using hip
  have hnonneg : 0 ≤ (i : ℝ) / (2 : ℝ) ^ k :=
    div_nonneg (Nat.cast_nonneg i) hp.le
  have hw : 0 ≤ 1 / (2 : ℝ) ^ k := one_div_nonneg.mpr hp.le
  have hright :
      -1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k =
        (-1 + (i : ℝ) / (2 : ℝ) ^ k) + 1 / (2 : ℝ) ^ k := by
    ring
  rw [hright] at hhi
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · apply abs_le.mpr
    constructor <;> linarith
