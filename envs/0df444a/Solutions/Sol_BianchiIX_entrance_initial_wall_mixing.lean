-- Prove2me | solution 1 for BianchiIX.entrance_initial_wall_mixing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:25.064876+00:00
-- url     : https://prove2.me/submissions/79cf7971-92c9-47bb-87b5-c854634e1edd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- Mixing of the two initial wall columns preserves their distinct amplitude factors. -/
theorem solution {k θ u v w X Y : ℝ}
    (hk : 1 ≤ k) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    (u * |X| + w * |Y|) * (u * v + (u * v * w + θ * (v * w) ^ 2) / k ^ 2) ≤
      3 * (u * v * |X| + (u * v * w + θ * (v * w) ^ 2) * |Y|) := by
  let P := u * v
  let S := u * v * w + θ * (v * w) ^ 2
  have hθ0 := hθ.1
  have hu0 := hu.1
  have hv0 := hv.1
  have hw0 := hw.1
  have hP : 0 ≤ P := mul_nonneg hu.1 hv.1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hPv : P ≤ v := by simpa using mul_le_mul_of_nonneg_right hu.2 hv.1
  have hPw : P * w ≤ v := (mul_le_of_le_one_right hP hw.2).trans hPv
  have hvw0 : 0 ≤ v * w := mul_nonneg hv.1 hw.1
  have hvw : v * w ≤ v := mul_le_of_le_one_right hv.1 hw.2
  have hvw1 : v * w ≤ 1 := hvw.trans hv.2
  have hsq' : (v * w) ^ 2 ≤ v * w := by nlinarith only [mul_le_mul_of_nonneg_left hvw1 hvw0]
  have hsq : (v * w) ^ 2 ≤ v := hsq'.trans hvw
  have htail : θ * (v * w) ^ 2 ≤ v :=
    (mul_le_of_le_one_left (sq_nonneg _) hθ.2).trans hsq
  have hSv : S ≤ 2 * v := by dsimp [S]; linarith only [hPw, htail]
  have hterm : P + S / k ^ 2 ≤ P + S :=
    add_le_add le_rfl (div_le_self hS (one_le_pow₀ hk))
  have hU : u * (P + S / k ^ 2) ≤ 3 * P := by
    have H := mul_le_mul_of_nonneg_left (hterm.trans (add_le_add hPv hSv)) hu.1
    dsimp [P] at H ⊢
    nlinarith only [H]
  have hW : w * (P + S / k ^ 2) ≤ 2 * S := by
    have H := mul_le_mul_of_nonneg_left hterm hw.1
    have HP : w * P ≤ S := by dsimp [P, S]; nlinarith only [mul_nonneg hθ.1 (sq_nonneg (v * w))]
    have HS : w * S ≤ S := mul_le_of_le_one_left hS hw.2
    nlinarith only [H, HP, HS]
  have H := add_le_add (mul_le_mul_of_nonneg_right hU (abs_nonneg X))
    (mul_le_mul_of_nonneg_right hW (abs_nonneg Y))
  change (u * |X| + w * |Y|) * (P + S / k ^ 2) ≤ 3 * (P * |X| + S * |Y|)
  nlinarith only [H, mul_nonneg hS (abs_nonneg Y)]
