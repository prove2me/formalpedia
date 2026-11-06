-- Prove2me | solution 1 for BianchiIX.connection_growing_endpoint_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:20.767205+00:00
-- url     : https://prove2.me/submissions/923cc269-b5af-4db6-a4e4-0f68e15629b8

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The growing initial response has uniform endpoint scales despite the logarithmic duration. -/
theorem solution {μ u w L : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000)
    (hL : w * L ≤ 1) :
    32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ ≤ 16 * μ / w ∧
    (12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2 ≤
      200 / (μ ^ 3 * w) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hwne := ne_of_gt hw.1
  have huμ : u * μ ≤ 1 / 10000 := (le_div_iff₀ hμ0).mp hu.2
  have hus : u ≤ 1 / 40000 := by nlinarith only [huμ, hμ, hu.1]
  have hsum : u + w ≤ 1 / 8000 := by linarith only [hus, hw.2]
  have hmix : w * L * (u + w) ≤ 1 / 8000 :=
    (mul_le_mul_of_nonneg_right hL (by linarith only [hu.1, hw.1])).trans (by simpa using hsum)
  have hcross : μ * u * w ≤ 1 / 100000000 := by
    have H := mul_le_mul_of_nonneg_right huμ hw.1.le
    nlinarith only [H, hw.2]
  have hscaled : 32 * μ * w ≤ μ := by nlinarith only [hw.2, hμ0]
  constructor
  · apply (le_div_iff₀ hw.1).mpr
    apply (mul_le_mul_iff_left₀ hμ0).mp
    have hid : ((32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ) * w) * μ =
        32 * μ * w + 12800 * (μ * u * w) + 96 + 1024000 * (w * L * (u + w)) := by
      field_simp
    rw [hid]
    nlinarith only [hscaled, hcross, hmix, hμ]
  · apply (le_div_iff₀ (mul_pos (pow_pos hμ0 3) hw.1)).mpr
    have hid : ((12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2) * (μ ^ 3 * w) =
        12800 * (μ * u * w) + 64 + 1024000 * (w * L * (u + w)) := by
      field_simp
    rw [hid]
    nlinarith only [hcross, hmix]
