-- Prove2me | solution 1 for BianchiIX.connection_strong_cone_size
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:34:42.591673+00:00
-- url     : https://prove2.me/submissions/247c9ac8-42de-43fa-b118-3a9eb046d845

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

private theorem BianchiIX.sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos x).le (Real.exp_pos (x / 2)).le).mpr
  rw [← Real.exp_add, add_halves]

/-- The strong row is uniformly small even when the radial parameter is unbounded. -/
theorem solution {μ ε u w L : ℝ} (hμ : 4 ≤ μ) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 < u ∧ u ≤ ε / μ) (hw : 0 < w ∧ w ≤ ε) (hL : 1 ≤ L) (hwexp : w = Real.exp (-L)) :
    (Real.sqrt u * Real.exp (-μ * L / 4)) *
      (274 * L + 9000 * (1 / u + L / μ) * Real.sqrt u + 32 * μ / w * Real.sqrt w) ≤ 20000 * Real.sqrt ε := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hue : u ≤ ε := hu.2.trans (div_le_self hε.1 (by linarith only [hμ]))
  have hsu := Real.sqrt_le_sqrt hue
  have hse := Real.sqrt_nonneg ε
  have hes : ε ≤ Real.sqrt ε := by
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε.2
    nlinarith only [Real.sq_sqrt hε.1, hs1, hse]
  let E := Real.exp (-μ * L / 4)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hEw : E ≤ w := by rw [hwexp]; exact Real.exp_le_exp.mpr (by nlinarith only [hμ, hL0])
  have hLE : L * E ≤ 1 := by
    have H := affine_mul_exp_neg_le_one L
    have H' := mul_le_mul_of_nonneg_left hEw hL0
    rw [hwexp] at H'
    nlinarith only [H, H', Real.exp_pos (-L)]
  have hcross : μ * Real.exp ((-μ / 4 + 1 / 2) * L) ≤ 8 := by
    have hx : (-μ / 4 + 1 / 2) * L ≤ -μ / 8 := by nlinarith only [hμ, hL]
    have H := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hμ0.le
    have H' := affine_mul_exp_neg_le_one (μ / 8)
    rw [show -(μ / 8) = -μ / 8 by ring] at H'
    nlinarith only [H, H', Real.exp_pos (-μ / 8)]
  have hwroot : Real.sqrt w / w = Real.exp (L / 2) := by
    rw [hwexp, sqrt_exp_half, ← Real.exp_sub]
    congr 1
    ring
  have hjoin : E * (Real.sqrt w / w) = Real.exp ((-μ / 4 + 1 / 2) * L) := by
    change Real.exp (-μ * L / 4) * (Real.sqrt w / w) = _
    rw [hwroot, ← Real.exp_add]
    congr 1
    ring
  have hid : (Real.sqrt u * E) *
      (274 * L + 9000 * (1 / u + L / μ) * Real.sqrt u + 32 * μ / w * Real.sqrt w) =
      274 * Real.sqrt u * (L * E) + 9000 * E + 9000 * (u / μ) * (L * E) +
        32 * Real.sqrt u * (μ * Real.exp ((-μ / 4 + 1 / 2) * L)) := by
    rw [← hjoin]
    calc
      _ = 274 * Real.sqrt u * (L * E) + 9000 * ((Real.sqrt u) ^ 2 / u) * E +
          9000 * ((Real.sqrt u) ^ 2 / μ) * (L * E) + 32 * Real.sqrt u * (μ * (E * (Real.sqrt w / w))) := by ring
      _ = _ := by rw [Real.sq_sqrt hu.1.le, div_self (ne_of_gt hu.1)]; ring
  rw [hid]
  have H1 : 274 * Real.sqrt u * (L * E) ≤ 274 * Real.sqrt ε := by
    have H := mul_le_mul hsu hLE (mul_nonneg hL0 hE0) hse
    nlinarith only [H]
  have H2 : 9000 * E ≤ 9000 * Real.sqrt ε := mul_le_mul_of_nonneg_left (hEw.trans (hw.2.trans hes)) (by norm_num)
  have H3 : 9000 * (u / μ) * (L * E) ≤ 9000 * Real.sqrt ε := by
    have huq : u / μ ≤ Real.sqrt ε :=
      (div_le_self hu.1.le (by linarith only [hμ])).trans (hue.trans hes)
    have H := mul_le_mul huq hLE (mul_nonneg hL0 hE0) hse
    nlinarith only [H]
  have H4 : 32 * Real.sqrt u * (μ * Real.exp ((-μ / 4 + 1 / 2) * L)) ≤ 256 * Real.sqrt ε := by
    have H := mul_le_mul hsu hcross (by positivity) hse
    nlinarith only [H]
  nlinarith only [H1, H2, H3, H4, hse]
