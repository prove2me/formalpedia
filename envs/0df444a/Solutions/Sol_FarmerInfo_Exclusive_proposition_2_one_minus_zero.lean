-- Prove2me | solution 1 for FarmerInfo.Exclusive.proposition_2_one_minus_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:42:05.022265+00:00
-- url     : https://prove2.me/submissions/39b00617-efcc-41b0-9df0-d3bb6ed71954

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

open MeasureTheory Finset FarmerInfo.Exclusive

theorem solution (M : Model) (hM : M.Standing) :
    M.W 1 - M.W 0 =
      M.β * M.V /
        (M.b * (2 * M.α + M.γ + (M.n : ℝ) * M.γ) ^ 2 *
          (4 * M.α ^ 2 + (1 + (M.n : ℝ)) * M.γ * (M.β + M.γ) +
            2 * M.α * (2 * M.β + (2 + (M.n : ℝ)) * M.γ)) ^ 2) := by
  obtain ⟨hn, ha, hb, hα, hβ, hγ⟩ := hM
  have hn0 : (0 : ℝ) ≤ M.n := Nat.cast_nonneg _
  have hP1 : M.Psi 1 = 2 * (4 * M.α ^ 2 + (1 + (M.n : ℝ)) * M.γ * (M.β + M.γ) +
            2 * M.α * (2 * M.β + (2 + (M.n : ℝ)) * M.γ)) := by unfold Model.Psi; ring
  have hP0 : M.Psi 0 = (2 * M.α + M.γ + (M.n : ℝ) * M.γ) * (2 * M.α + M.γ + 2 * M.β) := by
    unfold Model.Psi; ring
  have hX : 0 < 4 * M.α ^ 2 + (1 + (M.n : ℝ)) * M.γ * (M.β + M.γ) +
            2 * M.α * (2 * M.β + (2 + (M.n : ℝ)) * M.γ) := by positivity
  have hY : 0 < 2 * M.α + M.γ + (M.n : ℝ) * M.γ := by positivity
  have hZ : 0 < 2 * M.α + M.γ + 2 * M.β := by positivity
  unfold Model.W Model.WI Model.WJ Model.A1 Model.A2 Model.B1 Model.B0 Model.V
  rw [hP1, hP0]
  have hn1 : (M.n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring
