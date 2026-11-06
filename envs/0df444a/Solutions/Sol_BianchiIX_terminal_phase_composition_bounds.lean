-- Prove2me | solution 1 for BianchiIX.terminal_phase_composition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:21.861318+00:00
-- url     : https://prove2.me/submissions/1164fe06-f956-4ba6-9d6f-61c88e30e41b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open BianchiIX


/-- The terminal chain rule preserves the growing wall in the radial and old strong-wall columns. -/
theorem solution {α A B u v w Lr Lu Lv Lw Bu Bv : ℝ}
    (p q r s : Fin 3 → ℝ) (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hp : ∀ j, |p j| ≤ B / α ^ 2) (hq : ∀ j, |q j| ≤ B / α)
    (hr : ∀ j, |r j| ≤ B / α) (hs : ∀ j, |s j| ≤ B / α)
    (hBu : |Bu| ≤ B / α ^ 2) (hBv : |Bv| ≤ B / α ^ 2)
    (hLr : |Lr| ≤ A * u * v) (hLu : |Lu| ≤ A * α * v)
    (hLv : |Lv| ≤ A * u) (hLw : |Lw| ≤ A * α * u * v) :
    let D := fun j => Lr * p j + Lu * (u * q j) + Lv * (v * r j) + Lw * (w * s j)
    |D 0| + |D 1 + Lw * Bu| ≤ 10 * A * B * u * v / α ^ 2 ∧
      |D 2 + Lv * Bv| ≤ 10 * A * B * u / α ^ 2 ∧
      |Lv * Bv| ≤ A * B * u / α ^ 2 ∧ |Lw * Bu| ≤ A * B * u * v / α := by
  have ha : α ≠ 0 := hα.1.ne'
  have hα0 : 0 < α := hα.1
  have hv0 : 0 ≤ v := hv.1
  have hw0 : 0 ≤ w := hw.1
  have hαsq : α ^ 2 ≤ 1 := by nlinarith only [hα.1, hα.2]
  have hαsq' : α ^ 2 ≤ α := by nlinarith only [hα.1, hα.2]
  let T := A * B * u * v / α ^ 2
  let U := A * B * u / α ^ 2
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hbase : A * B * u * v ≤ T := by
    apply (le_div_iff₀ (sq_pos_of_pos hα.1)).mpr
    exact mul_le_of_le_one_right (by positivity) hαsq
  have hmid : A * B * u * v / α ≤ T :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hα.1) hαsq'
  have hTU : T ≤ U := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg α)
    exact mul_le_of_le_one_right (by positivity) hv.2
  have HD (j : Fin 3) : |Lr * p j + Lu * (u * q j) + Lv * (v * r j) + Lw * (w * s j)| ≤ 4 * T := by
    have H1 : |Lr * p j| ≤ T := by
      rw [abs_mul]
      exact (mul_le_mul hLr (hp j) (abs_nonneg _) (by positivity)).trans_eq (by dsimp only [T]; ring)
    have H2 : |Lu * (u * q j)| ≤ T := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu]
      calc
        _ ≤ (A * α * v) * (u * (B / α)) := mul_le_mul hLu
          (mul_le_mul_of_nonneg_left (hq j) hu) (by positivity) (by positivity)
        _ = A * B * u * v := by field_simp [ha]
        _ ≤ T := hbase
    have H3 : |Lv * (v * r j)| ≤ T := by
      rw [abs_mul, abs_mul, abs_of_nonneg hv.1]
      calc
        _ ≤ (A * u) * (v * (B / α)) := mul_le_mul hLv
          (mul_le_mul_of_nonneg_left (hr j) hv.1) (by positivity) (by positivity)
        _ = A * B * u * v / α := by ring
        _ ≤ T := hmid
    have H4 : |Lw * (w * s j)| ≤ T := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw.1]
      calc
        _ ≤ (A * α * u * v) * (w * (B / α)) := mul_le_mul hLw
          (mul_le_mul_of_nonneg_left (hs j) hw.1) (by positivity) (by positivity)
        _ = A * B * u * v * w := by field_simp [ha]
        _ ≤ A * B * u * v := mul_le_of_le_one_right (by positivity) hw.2
        _ ≤ T := hbase
    have HT := (abs_add_le (Lr * p j + Lu * (u * q j) + Lv * (v * r j)) (Lw * (w * s j))).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    linarith only [HT, H1, H2, H3, H4]
  have HV : |Lv * Bv| ≤ U := by
    rw [abs_mul]
    exact (mul_le_mul hLv hBv (abs_nonneg _) (by positivity)).trans_eq (by dsimp only [U]; ring)
  have HW : |Lw * Bu| ≤ A * B * u * v / α := by
    rw [abs_mul]
    exact (mul_le_mul hLw hBu (abs_nonneg _) (by positivity)).trans_eq (by field_simp [ha])
  dsimp only
  refine ⟨?_, ?_, HV, HW⟩
  · have H1 := (abs_add_le (Lr * p 1 + Lu * (u * q 1) + Lv * (v * r 1) + Lw * (w * s 1)) (Lw * Bu)).trans
      (add_le_add (HD 1) (HW.trans hmid))
    rw [show 10 * A * B * u * v / α ^ 2 = 10 * T by dsimp only [T]; ring]
    linarith only [HD 0, H1, hT]
  · have H2 := (abs_add_le (Lr * p 2 + Lu * (u * q 2) + Lv * (v * r 2) + Lw * (w * s 2)) (Lv * Bv)).trans
      (add_le_add (HD 2) HV)
    rw [show 10 * A * B * u / α ^ 2 = 10 * U by dsimp only [U]; ring]
    linarith only [H2, hTU, hU]
