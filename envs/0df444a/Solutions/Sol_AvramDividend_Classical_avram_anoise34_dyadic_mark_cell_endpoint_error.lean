-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise34_dyadic_mark_cell_endpoint_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:06:31.404127+00:00
-- url     : https://prove2.me/submissions/c41d393a-b1a9-46fb-98ed-cac70d69bc99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- A marked negative jump in a half-open dyadic cell lies within one cell
width of the chosen left-endpoint approximation. -/
theorem solution
    (n k i : ℕ) (z : ℝ)
    (hz : z ∈ (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ∩
      Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
        (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k))) :
    |z - (-1 + (i : ℝ) / (2 : ℝ) ^ k)| ≤ 1 / (2 : ℝ) ^ k := by
  rcases hz with ⟨_, ⟨hlo, hhi⟩⟩
  rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hlo))]
  calc
    z - (-1 + (i : ℝ) / (2 : ℝ) ^ k) ≤
        (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k) -
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) := sub_le_sub_right hhi _
    _ = 1 / (2 : ℝ) ^ k := by ring
