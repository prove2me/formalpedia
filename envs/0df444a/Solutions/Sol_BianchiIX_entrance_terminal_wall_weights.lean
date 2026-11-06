-- Prove2me | solution 1 for BianchiIX.entrance_terminal_wall_weights
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:51:43.654414+00:00
-- url     : https://prove2.me/submissions/39147dd4-0139-4f16-8625-c277b4227edb

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
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- Terminal wall products keep the weak decay and absorb the strong waiting factor. -/
theorem solution {k L u v w U W a c : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hu : 0 ≤ u ∧ u ≤ 1)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hU0 : 0 ≤ U) (hW0 : 0 ≤ W) (ha : 0 ≤ a ∧ a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hLa : L * a ≤ 3 / k) (hU : U ≤ u * v * a) (hW : W ≤ w * v * c) :
    (U + W) ^ 2 ≤ 2 * (u * v + v ^ 2 * w ^ 2 * c ^ 2) ∧
    k * L * (U + W) * U ≤ 6 * u * v ∧
    (L / k) * (U + W) * W ≤ 3 * u * v + (L / k) * (v ^ 2 * w ^ 2 * c ^ 2) ∧
    (U + W) * U ≤ 2 * u * v ∧
    (U + W) * W ≤ w * (u * v + v ^ 2 * w * c ^ 2) ∧
    U + W ≤ 2 * v := by
  have hk0 : 0 < k := by linarith
  have huv : 0 ≤ u * v := mul_nonneg hu.1 hv.1
  have hUb : U ≤ u * v := hU.trans (mul_le_of_le_one_right huv ha.2)
  have hWb : W ≤ w * v := hW.trans (mul_le_of_le_one_right (mul_nonneg hw.1 hv.1) hc.2)
  have hUv : U ≤ v := hUb.trans (mul_le_of_le_one_left hv.1 hu.2)
  have hWv : W ≤ v := hWb.trans (mul_le_of_le_one_left hv.1 hw.2)
  have hU1 : U ≤ 1 := hUv.trans hv.2
  have hW1 : W ≤ 1 := hWv.trans hv.2
  have hWw : W ≤ w := hWb.trans (mul_le_of_le_one_right hw.1 hv.2)
  have hsum : U + W ≤ 2 * v := by linarith only [hUv, hWv]
  have hUsq : U ^ 2 ≤ u * v := by nlinarith only [hUb, mul_le_of_le_one_right hU0 hU1]
  have hWsq : W ^ 2 ≤ v ^ 2 * w ^ 2 * c ^ 2 := by
    convert! pow_le_pow_left₀ hW0 hW 2 using 1
    ring
  have hfast : (U + W) * U ≤ 2 * (u * v * a) :=
    (mul_le_mul (by linarith only [hsum, hv.2] : U + W ≤ 2) hU hU0 (by norm_num)).trans_eq (by ring)
  have hcross : U * W ≤ u * v * a :=
    (mul_le_of_le_one_right hU0 hW1).trans hU
  have hslow : (U + W) * W ≤ u * v * a + v ^ 2 * w ^ 2 * c ^ 2 := by
    nlinarith only [hcross, hWsq]
  have hLk : L * a / k ≤ 3 := (div_le_self (mul_nonneg hL ha.1) hk).trans
    (hLa.trans (div_le_self (by norm_num) hk))
  refine ⟨?_, ?_, ?_, hfast.trans ?_, ?_, hsum⟩
  · nlinarith only [hUsq, hWsq, sq_nonneg (U - W)]
  · have H := mul_le_mul_of_nonneg_left hfast (mul_nonneg hk0.le hL)
    have HL := (le_div_iff₀ hk0).mp hLa
    have HC := mul_le_mul_of_nonneg_left HL (show 0 ≤ 2 * (u * v) by positivity)
    nlinarith only [H, HC]
  · calc
      _ = (L / k) * ((U + W) * W) := by ring
      _ ≤ (L / k) * (u * v * a + v ^ 2 * w ^ 2 * c ^ 2) :=
        mul_le_mul_of_nonneg_left hslow (div_nonneg hL hk0.le)
      _ = u * v * (L * a / k) + (L / k) * (v ^ 2 * w ^ 2 * c ^ 2) := by ring
      _ ≤ u * v * 3 + (L / k) * (v ^ 2 * w ^ 2 * c ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hLk huv) le_rfl
      _ = _ := by ring
  · nlinarith only [mul_le_of_le_one_right huv ha.2]
  · have H := mul_le_mul hUb hWw hW0 huv
    nlinarith only [H, hWsq]
