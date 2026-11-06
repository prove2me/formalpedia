-- Prove2me | solution 1 for BianchiIX.partial_core_radius_arrival_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:28:24.01421+00:00
-- url     : https://prove2.me/submissions/8cf27388-4818-4bd3-9e2b-93fe46cf3901

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contracted_radius_error {s q r v : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |s * q - v| ≤ |q - r| + |r - v| + |s - 1| * |v| := by
  have H := abs_sub_le (s * q) (s * v) v
  rw [← mul_sub, ← sub_one_mul, abs_mul, abs_mul, abs_of_nonneg hs] at H
  exact H.trans ((add_le_add (mul_le_of_le_one_left (abs_nonneg _) hs1) (le_refl _)).trans
    (add_le_add (abs_sub_le q r v) (le_refl _)))

end
end

private theorem BianchiIX.partial_core_moving_budget_absorption {k U P dR dU dP dz : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hsmall : U + P ≤ 1) :
    (U + P) * (|dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz|) / k ≤
      (U + P) * (|dR| + |dP|) / k + |dU| + 2 * (k * U + P ^ 2 / k) * |dz| := by
  have hk0 : 0 < k := by linarith only [hk]
  have hP1 : P ≤ 1 := by linarith only [hsmall, hU]
  have hk3 : 1 ≤ k ^ 3 := by nlinarith only [hk, sq_nonneg (k - 1)]
  have hz : (U + P) * (k ^ 2 * U + P / k) / k ≤ 2 * (k * U + P ^ 2 / k) := by
    have h₁ := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (pow_nonneg hk0.le 3) hU)
    have h₂ := mul_le_mul_of_nonneg_left hP1 hU
    have h₃ := mul_le_mul_of_nonneg_right hk3 hU
    have h₄ := mul_le_mul_of_nonneg_right (show 1 ≤ k by linarith only [hk]) (sq_nonneg P)
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hk0)).mp
    field_simp
    nlinarith only [h₁, h₂, h₃, h₄]
  have hu := mul_le_mul_of_nonneg_right hsmall (abs_nonneg dU)
  have hz' := mul_le_mul_of_nonneg_right hz (abs_nonneg dz)
  have hid : (U + P) * (|dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz|) / k =
      (U + P) * (|dR| + |dP|) / k + (U + P) * |dU| +
        ((U + P) * (k ^ 2 * U + P / k) / k) * |dz| := by field_simp; ring
  rw [hid]
  linarith only [hu, hz']


/-- Contract the final radial correction before absorbing the moving-start budget. -/
theorem solution {k U P K s q r X dR dU dP dz : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hP : 0 ≤ P) (hsmall : U + P ≤ 1) (hK : 1 ≤ K)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hse : |s - 1| ≤ 8 * (U / k + P ^ 2 / k ^ 2))
    (hr : |r - dR| ≤ 2 * (k * U + P ^ 2 / k) * |dz|)
    (hX : X ≤ k * |dU| + 2 * k ^ 2 * U * |dz|)
    (hd : |q - r| ≤ 256 * (X / k + (U + P) *
      ((4 * K) * (|dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz|)) / k)) :
    |s * q - dR| ≤ 4096 * K *
      (|dU| + (U + P) * (|dR| + |dP|) / k + (k * U + P ^ 2 / k) * |dz|) := by
  let B := (U + P) * (|dR| + |dP|) / k
  let L := (k * U + P ^ 2 / k) * |dz|
  let N := |dU| + B + L
  let Q₀ := |dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz|
  have hk0 : 0 < k := by linarith only [hk]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hbudget : (U + P) * Q₀ / k ≤ 2 * N := by
    have H := partial_core_moving_budget_absorption hk hU hsmall
      (dR := dR) (dU := dU) (dP := dP) (dz := dz)
    rw [mul_assoc 2 (k * U + P ^ 2 / k) |dz|] at H
    change (U + P) * Q₀ / k ≤ B + |dU| + 2 * L at H
    dsimp [N]
    linarith only [H, hB, abs_nonneg dU]
  have hX' : X / k ≤ 2 * N := by
    have H := div_le_div_of_nonneg_right hX hk0.le
    have heq : (k * |dU| + 2 * k ^ 2 * U * |dz|) / k = |dU| + 2 * k * U * |dz| := by
      field_simp
    rw [heq] at H
    have hL' : k * U * |dz| ≤ L := by
      dsimp [L]
      nlinarith only [mul_nonneg (div_nonneg (sq_nonneg P) hk0.le) (abs_nonneg dz)]
    dsimp [N]
    linarith only [H, hL', hB, abs_nonneg dU]
  have hr' : |r - dR| ≤ 2 * N := by
    rw [mul_assoc 2 (k * U + P ^ 2 / k) |dz|] at hr
    change |r - dR| ≤ 2 * L at hr
    dsimp [N]
    linarith only [hr, hB, abs_nonneg dU]
  have hPk : P ≤ k := by linarith only [hsmall, hU, hk]
  have hscoef : U / k + P ^ 2 / k ^ 2 ≤ (U + P) / k := by
    have H := mul_le_mul_of_nonneg_left hPk hP
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hk0)).mp
    field_simp
    nlinarith only [H]
  have hse' : |s - 1| * |dR| ≤ 8 * N := by
    have H := (mul_le_mul_of_nonneg_right hse (abs_nonneg dR)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscoef (by norm_num : (0 : ℝ) ≤ 8))
        (abs_nonneg dR))
    have HB : ((U + P) / k) * |dR| ≤ B := by
      have HH := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (a := |dR|) (abs_nonneg dP))
        (div_nonneg (add_nonneg hU hP) hk0.le)
      convert! HH using 1
      dsimp [B]
      ring
    dsimp [N]
    nlinarith only [H, HB, hL, abs_nonneg dU]
  have hd' : |q - r| ≤ 512 * N + 2048 * K * N := by
    have HB := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 4 * K by positivity)
    have heq : (U + P) * ((4 * K) * Q₀) / k = (4 * K) * ((U + P) * Q₀ / k) := by ring
    change |q - r| ≤ 256 * (X / k + (U + P) * ((4 * K) * Q₀) / k) at hd
    rw [heq] at hd
    linarith only [hd, hX', HB]
  have H := (contracted_radius_error hs hs1).trans (add_le_add (add_le_add hd' hr') hse')
  have HKN := mul_le_mul_of_nonneg_right hK hN
  change |s * q - dR| ≤ 4096 * K * N
  nlinarith only [H, HKN, hN]
