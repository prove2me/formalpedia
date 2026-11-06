-- Prove2me | solution 1 for BianchiIX.coreBootstrap_coefficient_scales
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:58:54.354986+00:00
-- url     : https://prove2.me/submissions/981dc575-9222-401d-93e8-40c316ae3e16

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {k r : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k) :
    let m := (1 / 10000) / k
    5 ≤ r ∧ 0 ≤ m ∧ m ≤ 1 / 100 ∧ r * m ≤ 1 / 1000 ∧
    m / r ≤ 1 / 100 ∧ k / r ≤ 3 / 2 ∧ k ^ 2 / r ^ 2 ≤ 3 / 2 ∧
    4 * m ^ 2 / r ≤ m / 10 := by
  let m := (1 / 10000) / k
  have hk0 : 0 < k := by linarith
  have hr5 : 5 ≤ r := by linarith [hr.1]
  have hr0 : 0 < r := by linarith
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm : m ≤ 1 / 100 := (div_le_iff₀ hk0).mpr (by linarith)
  have hrm : r * m ≤ 1 / 1000 := by
    dsimp [m]
    rw [← mul_div_assoc, div_le_iff₀ hk0]
    linarith [hr.2]
  have hmr : m / r ≤ 1 / 100 := (div_le_iff₀ hr0).mpr (by linarith)
  refine ⟨hr5, hm0, hm, hrm, hmr,
    (div_le_iff₀ hr0).mpr (by linarith [hr.1]),
    (div_le_iff₀ (sq_pos_of_pos hr0)).mpr ?_, ?_⟩
  · have H := (sq_le_sq₀ (show 0 ≤ 99 / 100 * k by positivity) hr0.le).mpr hr.1
    nlinarith
  · have H := mul_le_mul_of_nonneg_left hmr hm0
    calc
      4 * m ^ 2 / r = 4 * (m * (m / r)) := by ring
      _ ≤ m / 10 := by nlinarith
