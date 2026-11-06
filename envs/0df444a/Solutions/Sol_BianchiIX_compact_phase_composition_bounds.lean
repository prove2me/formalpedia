-- Prove2me | solution 1 for BianchiIX.compact_phase_composition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:24.306327+00:00
-- url     : https://prove2.me/submissions/55d4b28d-b98c-46e6-9e05-30b17dc63f25

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open BianchiIX


/-- The small weak-wall factor survives composition with a bounded finite passage. -/
theorem solution {A B x y E Lr Lu Lv Bu Bv : ℝ}
    (p q r : Fin 3 → ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : x + y ≤ 1)
    (hp : ∀ j, |p j| ≤ A) (hq : ∀ j, |q j| ≤ A) (hr : ∀ j, |r j| ≤ A)
    (hBu : |Bu| ≤ A) (hBv : |Bv| ≤ A)
    (hE : |E| ≤ B * A ^ 2 * y * (x + y))
    (hLr : |Lr| ≤ B * A ^ 2 * y * (x + y))
    (hLu : |Lu| ≤ B * A * y) (hLv : |Lv| ≤ B * A * (x + y)) :
    let D := fun j => Lr * p j + Lu * (x * q j) + Lv * (y * r j)
    let C := B * A ^ 2 * (A + 3)
    |E| + |D 0| ≤ C * y * (x + y) ∧
      |D 1 + Lu * Bu| ≤ C * y ∧ |D 2 + Lv * Bv| ≤ C * (x + y) := by
  let T := B * A ^ 2
  have hT : 0 ≤ T := mul_nonneg hB (sq_nonneg A)
  have hb0 : 0 ≤ x + y := add_nonneg hx hy
  have hya : y ≤ 1 := by linarith only [hx, hb]
  have hD (j : Fin 3) : |Lr * p j + Lu * (x * q j) + Lv * (y * r j)| ≤
      T * (A + 2) * y * (x + y) := by
    have h1 : |Lr * p j| ≤ T * A * y * (x + y) := by
      rw [abs_mul]
      calc
        _ ≤ (B * A ^ 2 * y * (x + y)) * A := mul_le_mul hLr (hp j) (abs_nonneg _) (by positivity)
        _ = _ := by dsimp only [T]; ring
    have h2 : |Lu * (x * q j)| ≤ T * y * (x + y) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx]
      calc
        _ ≤ (B * A * y) * (x * A) := mul_le_mul hLu
          (mul_le_mul_of_nonneg_left (hq j) hx) (by positivity) (by positivity)
        _ = T * y * x := by dsimp only [T]; ring
        _ ≤ T * y * (x + y) := mul_le_mul_of_nonneg_left (by linarith only [hy]) (mul_nonneg hT hy)
    have h3 : |Lv * (y * r j)| ≤ T * y * (x + y) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hy]
      calc
        _ ≤ (B * A * (x + y)) * (y * A) := mul_le_mul hLv
          (mul_le_mul_of_nonneg_left (hr j) hy) (by positivity) (by positivity)
        _ = _ := by dsimp only [T]; ring
    calc
      _ ≤ |Lr * p j| + |Lu * (x * q j)| + |Lv * (y * r j)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ T * A * y * (x + y) + T * y * (x + y) + T * y * (x + y) :=
        add_le_add (add_le_add h1 h2) h3
      _ = _ := by ring
  have hu : |Lu * Bu| ≤ T * y := by
    rw [abs_mul]
    calc
      _ ≤ (B * A * y) * A := mul_le_mul hLu hBu (abs_nonneg _) (by positivity)
      _ = _ := by dsimp only [T]; ring
  have hv : |Lv * Bv| ≤ T * (x + y) := by
    rw [abs_mul]
    calc
      _ ≤ (B * A * (x + y)) * A := mul_le_mul hLv hBv (abs_nonneg _) (by positivity)
      _ = _ := by dsimp only [T]; ring
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ T * y * (x + y) + T * (A + 2) * y * (x + y) := add_le_add hE (hD 0)
      _ = _ := by dsimp only [T]; ring
  · calc
      _ ≤ |Lr * p 1 + Lu * (x * q 1) + Lv * (y * r 1)| + |Lu * Bu| := abs_add_le _ _
      _ ≤ T * (A + 2) * y * (x + y) + T * y := add_le_add (hD 1) hu
      _ ≤ T * (A + 2) * y * 1 + T * y := add_le_add
        (mul_le_mul_of_nonneg_left hb (by positivity)) le_rfl
      _ = _ := by dsimp only [T]; ring
  · calc
      _ ≤ |Lr * p 2 + Lu * (x * q 2) + Lv * (y * r 2)| + |Lv * Bv| := abs_add_le _ _
      _ ≤ T * (A + 2) * y * (x + y) + T * (x + y) := add_le_add (hD 2) hv
      _ ≤ T * (A + 2) * 1 * (x + y) + T * (x + y) := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hya (by positivity)) hb0) le_rfl
      _ = _ := by dsimp only [T]; ring
