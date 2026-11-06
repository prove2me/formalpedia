-- Prove2me | solution 1 for BianchiIX.homogeneous_solution_eq_exp_integral_Icc
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:56:01.513206+00:00
-- url     : https://prove2.me/submissions/8ab0f941-52b3-4902-874f-a16a0fbdc02b

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- The integrating factor formula on a closed segment, including zero initial data. -/
theorem solution {f r : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : ContinuousOn r (Icc a b)) (hc : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (r t * f t) t) :
    f b = f a * Real.exp (∫ t in a..b, r t) := by
  let P : ℝ → ℝ := fun t => ∫ s in a..t, r s
  have hri : IntervalIntegrable r volume a b := hr.intervalIntegrable_of_Icc hab
  have hPc : ContinuousOn P (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hri left_mem_uIcc
  have hPi (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt P (r t) t := by
    have hro := hr.mono Ioo_subset_Icc_self
    exact intervalIntegral.integral_hasDerivAt_right
      ((hr.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      (hro.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hro.continuousAt (isOpen_Ioo.mem_nhds ht))
  have hF (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => f s * Real.exp (-P s)) 0 t := by
    convert! (hf t ht).mul (hPi t ht).neg.exp using 1
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hc.mul (Real.continuous_exp.comp_continuousOn hPc.neg)) hF
    (intervalIntegrable_const (c := (0 : ℝ)))
  have heq : f b * Real.exp (-P b) = f a := by
    simpa [P, sub_eq_zero] using H.symm
  calc
    f b = (f b * Real.exp (-P b)) * Real.exp (P b) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = f a * Real.exp (P b) := by rw [heq]
