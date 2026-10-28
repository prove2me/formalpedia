-- Prove2me | solution 1 for AvramDividend.Classical.killed_lintegral_ofReal_scaled_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:47:31.672644+00:00
-- url     : https://prove2.me/submissions/67d2f154-da53-469a-b858-defee0bc3d26

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Classical
open scoped NNReal ENNReal
/-! Scaling killed lower integrals by a nonnegative payment size. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (f : Ω → ℝ) (k r : ℝ)
    (hr : 0 ≤ r)
    (hbase : ENNReal.ofReal k ≤
      (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (f ω) else 0 ∂P)) :
    ENNReal.ofReal (r * k) ≤
      (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (r * f ω) else 0 ∂P) := by
  have hscaled :
      ENNReal.ofReal r * ENNReal.ofReal k ≤
        ENNReal.ofReal r *
          (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (f ω) else 0 ∂P) :=
    mul_le_mul_right hbase (ENNReal.ofReal r)
  calc
    ENNReal.ofReal (r * k) =
        ENNReal.ofReal r * ENNReal.ofReal k :=
      ENNReal.ofReal_mul hr
    _ ≤ ENNReal.ofReal r *
        (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (f ω) else 0 ∂P) :=
      hscaled
    _ = (∫⁻ ω, ENNReal.ofReal r *
        (if ω ∈ S then ENNReal.ofReal (f ω) else 0) ∂P) :=
      (lintegral_const_mul' (ENNReal.ofReal r)
        (fun ω => if ω ∈ S then ENNReal.ofReal (f ω) else 0)
        (by simp)).symm
    _ = (∫⁻ ω, if ω ∈ S then ENNReal.ofReal (r * f ω) else 0 ∂P) := by
      apply lintegral_congr
      intro ω
      by_cases hS : ω ∈ S
      · simp only [if_pos hS]
        exact (ENNReal.ofReal_mul hr).symm
      · simp [hS]
