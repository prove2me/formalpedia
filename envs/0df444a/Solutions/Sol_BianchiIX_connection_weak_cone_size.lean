-- Prove2me | solution 1 for BianchiIX.connection_weak_cone_size
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:52:04.512267+00:00
-- url     : https://prove2.me/submissions/bdfbe608-a59e-412b-b85d-6fe3729a1ff8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The weak row retains an exponential margin on the entire long-connection region. -/
theorem solution {μ u w L : ℝ} (hμ : 4 ≤ μ) (hu : 0 ≤ u ∧ u ≤ 1)
    (hw : 0 < w) (hL : 256 ≤ L) (hsmall : 40000 * Real.sqrt w ≤ 1) :
    (Real.sqrt w * Real.exp (-L / μ)) *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u +
        (1 + 32 / μ) / w * Real.sqrt w) ≤ Real.exp (-L / (2 * μ)) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hsu : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr hu.2
  have hsw := Real.sqrt_nonneg w
  have hrow : 274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u ≤
      10000 * (1 + L) / μ ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hsu (show 0 ≤ 9000 * (1 + L) / μ ^ 2 by positivity)
    have HH := div_le_div_of_nonneg_right (show 274 * L ≤ 1000 * (1 + L) by linarith only [hL0]) (sq_nonneg μ)
    calc
      _ ≤ 1000 * (1 + L) / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 := by linarith only [H, HH]
      _ = _ := by ring
  have hsmall' : 10000 * Real.sqrt w ≤ 1 / 4 := by linarith only [hsmall]
  have hcorr : 32 / μ + 10000 * (1 + L) * Real.sqrt w / μ ^ 2 ≤ L / (4 * μ) := by
    have H := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ 1 + L by positivity)
    apply (le_div_iff₀ (by positivity : 0 < 4 * μ)).mpr
    field_simp
    have Hμ := mul_le_mul_of_nonneg_left hμ hL0
    nlinarith only [H, Hμ, hL, hμ]
  have hid : (Real.sqrt w * Real.exp (-L / μ)) *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u +
        (1 + 32 / μ) / w * Real.sqrt w) =
      Real.exp (-L / μ) * (1 + 32 / μ + Real.sqrt w *
        (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u)) := by
    calc
      _ = Real.exp (-L / μ) * ((1 + 32 / μ) * ((Real.sqrt w) ^ 2 / w) +
        Real.sqrt w * (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u)) := by ring
      _ = _ := by rw [Real.sq_sqrt hw.le, div_self (ne_of_gt hw)]; ring
  rw [hid]
  have Hb : 1 + 32 / μ + Real.sqrt w *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u) ≤ 1 + L / (4 * μ) := by
    have H := mul_le_mul_of_nonneg_left hrow hsw
    have HH : Real.sqrt w * (10000 * (1 + L) / μ ^ 2) = 10000 * (1 + L) * Real.sqrt w / μ ^ 2 := by ring
    rw [HH] at H
    linarith only [H, hcorr]
  calc
    _ ≤ Real.exp (-L / μ) * (1 + L / (4 * μ)) := mul_le_mul_of_nonneg_left Hb (Real.exp_pos _).le
    _ ≤ Real.exp (-L / μ) * Real.exp (L / (4 * μ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (L / (4 * μ))]) (Real.exp_pos _).le
    _ = Real.exp (-3 * L / (4 * μ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-L / (2 * μ)) := Real.exp_le_exp.mpr (by apply (div_le_div_iff₀ (by positivity : 0 < 4 * μ) (by positivity : 0 < 2 * μ)).mpr; nlinarith only [hL0, hμ0])
