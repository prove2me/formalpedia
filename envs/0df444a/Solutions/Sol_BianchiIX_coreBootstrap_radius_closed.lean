-- Prove2me | solution 1 for BianchiIX.coreBootstrap_radius_closed
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:32:21.531958+00:00
-- url     : https://prove2.me/submissions/6fc1b9ea-687c-43fa-b173-ee9036662b6b

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


theorem solution {k r : ℝ} (hk : 6 ≤ k) (hr : 0 ≤ r)
    (he : |r ^ 2 - k ^ 2| ≤ 1 / 8) : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k := by
  obtain ⟨hl, hu⟩ := abs_le.mp he
  constructor
  · by_contra! hlt
    have hs : r ^ 2 < (99 / 100 * k) ^ 2 := (sq_lt_sq₀ hr (by linarith)).mpr hlt
    nlinarith
  · by_contra! hgt
    have hs : (101 / 100 * k) ^ 2 < r ^ 2 := (sq_lt_sq₀ (by linarith) hr).mpr hgt
    nlinarith
