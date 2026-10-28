-- Prove2me | solution 1 for AvramDividend.Classical.full_convolution_monotone_of_monotone_first
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:59:36.719981+00:00
-- url     : https://prove2.me/submissions/622d62ae-9607-4f2b-a6e4-5714c57cb390

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory

theorem solution
    (f g : ℝ → ℝ)
    (hf : Monotone f)
    (hg : ∀ y : ℝ, 0 ≤ g y)
    (hInt : ∀ x : ℝ, Integrable (fun y : ℝ => f (x - y) * g y) volume) :
    Monotone (fun x : ℝ =>
      ∫ y : ℝ, f (x - y) * g y ∂volume) := by
  intro a b hab
  exact integral_mono (hInt a) (hInt b) fun y =>
    mul_le_mul_of_nonneg_right (hf (by linarith)) (hg y)
