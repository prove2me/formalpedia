-- Prove2me | solution 1 for BianchiIX.entrance_terminal_wall_forms
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:26.847974+00:00
-- url     : https://prove2.me/submissions/53df725b-68e2-46bd-b839-7346f38879c5

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


/-- Terminal products control all three logarithmic columns without further waiting estimates. -/
theorem solution {A k u v w U W θ ω : ℝ}
    (hA : 0 ≤ A) (hk : 1 ≤ k) (hu : 0 < u ∧ u ≤ 1) (hv : 0 < v ∧ v ≤ 1)
    (hw : 0 < w ∧ w ≤ 1) (hU : 0 ≤ U) (hW : 0 ≤ W) (hθ : 0 ≤ θ) (hω : 0 ≤ ω ∧ ω ≤ 1)
    (hsq : (U + W) ^ 2 ≤ 2 * (u * v + v ^ 2 * w ^ 2 * ω))
    (hfast : (U + W) * U ≤ 2 * u * v)
    (hslow : (U + W) * W ≤ w * (u * v + v ^ 2 * w * ω))
    (hsum : U + W ≤ 2 * v) :
    let b := U + W
    let J := u * v + v ^ 2 * w * (θ + ω)
    let K := u + v * w ^ 2
    b ^ 2 / k ^ 2 ≤ 4 ∧
    b / k * (U * (1 / u + A) + W * (A / k ^ 2)) ≤ (2 + 4 * A) * (v / k) ∧
    b / k * (U * A + W * (1 / w + A / k ^ 2)) ≤ (2 + 4 * A) * (J / k) ∧
    b / k * (U * (A * k / v) + W * (A / v)) ≤ (2 + 4 * A) * K := by
  intro b J K
  have hk0 : 0 < k := by linarith
  have hb : 0 ≤ b := add_nonneg hU hW
  have hJ : 0 ≤ J := by dsimp [J]; positivity [hu.1, hv.1, hw.1, hω.1]
  have hK : 0 ≤ K := by dsimp [K]; positivity [hu.1, hv.1]
  have hAk : A / k ^ 2 ≤ A := div_le_self hA (one_le_pow₀ hk)
  have hb2v : b ^ 2 ≤ 4 * v := by
    have H := pow_le_pow_left₀ hb hsum 2
    nlinarith only [H, mul_le_mul_of_nonneg_left hv.2 hv.1.le]
  have hb2 : b ^ 2 ≤ 4 := by linarith only [hb2v, hv.2]
  have htail : u * v + v ^ 2 * w ^ 2 * ω ≤ J := by
    have hw2 : w ^ 2 ≤ w := by nlinarith only [mul_le_mul_of_nonneg_left hw.2 hw.1.le]
    have H := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ v ^ 2 * ω by positivity [hω.1])
    have HP : 0 ≤ v ^ 2 * w * θ := by positivity [hw.1]
    dsimp [J]
    nlinarith only [H, HP]
  have hb2J : b ^ 2 ≤ 2 * J := hsq.trans (mul_le_mul_of_nonneg_left htail (by norm_num))
  have hslowJ : b * W ≤ w * J := hslow.trans
    (mul_le_mul_of_nonneg_left (by dsimp [J]; nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg v) hw.1.le) hθ]) hw.1.le)
  have hslowK : b * W ≤ v * K := by
    have H1 := mul_le_mul_of_nonneg_left hw.2 (show 0 ≤ u * v by positivity [hu.1, hv.1])
    have H2 := mul_le_mul_of_nonneg_left hω.2 (show 0 ≤ v ^ 2 * w ^ 2 by positivity)
    dsimp [b, K]
    nlinarith only [hslow, H1, H2]
  have hfastu : b * U / u ≤ 2 * v := (div_le_iff₀ hu.1).mpr (by nlinarith only [hfast])
  have hsloww : b * W / w ≤ J := (div_le_iff₀ hw.1).mpr (by nlinarith only [hslowJ])
  have hfastv : b * U / v ≤ 2 * u := (div_le_iff₀ hv.1).mpr (by nlinarith only [hfast])
  have hslowv : b * W / v ≤ K := (div_le_iff₀ hv.1).mpr (by nlinarith only [hslowK])
  refine ⟨(div_le_self (sq_nonneg b) (one_le_pow₀ hk)).trans hb2, ?_, ?_, ?_⟩
  · calc
      _ ≤ b / k * (U * (1 / u + A) + W * A) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hAk hW)) (by positivity)
      _ = (b * U / u + A * b ^ 2) / k := by dsimp [b]; ring
      _ ≤ (2 * v + A * (4 * v)) / k := div_le_div_of_nonneg_right
        (add_le_add hfastu (mul_le_mul_of_nonneg_left hb2v hA)) hk0.le
      _ = _ := by ring
  · calc
      _ ≤ b / k * (U * A + W * (1 / w + A)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hAk) hW)) (by positivity)
      _ = (b * W / w + A * b ^ 2) / k := by dsimp [b]; ring
      _ ≤ (J + A * (2 * J)) / k := div_le_div_of_nonneg_right
        (add_le_add hsloww (mul_le_mul_of_nonneg_left hb2J hA)) hk0.le
      _ ≤ ((2 + 4 * A) * J) / k := div_le_div_of_nonneg_right (by nlinarith only [hJ, mul_nonneg hA hJ]) hk0.le
      _ = _ := by ring
  · have hslowvk : b * W / v / k ≤ K :=
      (div_le_self (div_nonneg (mul_nonneg hb hW) hv.1.le) hk).trans hslowv
    calc
      _ = A * (b * U / v + b * W / v / k) := by field_simp
      _ ≤ A * (2 * u + K) := mul_le_mul_of_nonneg_left (add_le_add hfastv hslowvk) hA
      _ ≤ (2 + 4 * A) * K := by
        have huK : u ≤ K := le_add_of_nonneg_right (mul_nonneg hv.1.le (sq_nonneg w))
        have H := mul_le_mul_of_nonneg_left huK hA
        nlinarith only [H, hK, mul_nonneg hA hK]
