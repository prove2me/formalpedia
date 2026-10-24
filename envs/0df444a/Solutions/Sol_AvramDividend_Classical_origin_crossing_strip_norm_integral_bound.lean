-- Prove2me | solution 1 for AvramDividend.Classical.origin_crossing_strip_norm_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:11:37.874819+00:00
-- url     : https://prove2.me/submissions/241bdf03-79ac-4284-938e-13632fd929bc

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

-- Integrating a uniform linear jump bound over a jump-sized strip is quadratic.
theorem solution
    (f : ℝ → ℝ) (y C : ℝ) (hy : y < 0)
    (hf : IntegrableOn (fun x : ℝ => |f x|) (Ioo 0 (-y)))
    (hbound : ∀ x ∈ Ioo (0 : ℝ) (-y), |f x| ≤ C * (-y)) :
    (∫ x in Ioo (0 : ℝ) (-y), |f x|) ≤ C * y ^ 2 := by
  have hfinite : volume (Ioo (0 : ℝ) (-y)) ≠ ⊤ := by
    simp [Real.volume_Ioo]
  have hconst : IntegrableOn (fun _ : ℝ => C * (-y)) (Ioo 0 (-y)) volume := by
    exact integrableOn_const (hs := hfinite)
  calc
    (∫ x in Ioo (0 : ℝ) (-y), |f x|) ≤
        ∫ x in Ioo (0 : ℝ) (-y), C * (-y) := by
      exact setIntegral_mono_on hf hconst measurableSet_Ioo hbound
    _ = C * y ^ 2 := by
      rw [setIntegral_const]
      have hv : (volume (Ioo (0 : ℝ) (-y))).toReal = -y := by
        simp [Real.volume_Ioo, le_of_lt hy]
      change (volume (Ioo (0 : ℝ) (-y))).toReal * (C * (-y)) = C * y ^ 2
      rw [hv]
      ring
