-- Prove2me | solution 1 for AvramDividend.Classical.full_convolution_powers_monotone_of_nonnegative_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:03:59.919463+00:00
-- url     : https://prove2.me/submissions/6a88d58c-c410-4d66-bea3-a7f0bdec485a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκmono : Monotone κ)
    (hκpos : ∀ y : ℝ, 0 ≤ κ y)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hInt : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume) :
    ∀ n : ℕ, Monotone (F n) := by 
  intro n
  induction n with
  | zero => rw [hF0]; exact hκmono
  | succ n ih =>
    rw [hFsucc n]
    intro a b hab
    exact integral_mono (hInt n a) (hInt n b) fun y =>
      mul_le_mul_of_nonneg_left (ih (by linarith)) (hκpos y)
