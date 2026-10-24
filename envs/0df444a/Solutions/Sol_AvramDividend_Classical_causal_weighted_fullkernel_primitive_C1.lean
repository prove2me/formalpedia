-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_fullkernel_primitive_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:13:26.943762+00:00
-- url     : https://prove2.me/submissions/1503ac66-56de-489d-99d9-cc7189bffd47

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_primitive_contDiff_one
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The exponentially damped signed Volterra kernel has a C1 primitive on positive time. -/
theorem solution
    (K : ℝ → ℝ) (w β : ℝ) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ t in (0 : ℝ)..x,
        Real.exp (-w * t) * (β + K t)) (Ioi 0) := by
  have hExp : IntegrableOn (fun t : ℝ => Real.exp (-w * t))
      (Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using
      (AvramDividend.Classical.positive_laplace_constant_reference w hw).1
  have hKExp := AvramDividend.Classical.causal_l1_exponential_damping_integrable
    K w hw hK
  have hSum : IntegrableOn
      (fun t : ℝ => β * Real.exp (-w * t) +
        Real.exp (-w * t) * K t) (Ioi (0 : ℝ)) volume :=
    (hExp.const_mul β).add hKExp
  have hEq :
      (fun t : ℝ => Real.exp (-w * t) * (β + K t)) =
      (fun t : ℝ => β * Real.exp (-w * t) +
        Real.exp (-w * t) * K t) := by
    funext t
    ring
  have hFull : IntegrableOn
      (fun t : ℝ => Real.exp (-w * t) * (β + K t))
      (Ioi (0 : ℝ)) volume := by
    rw [hEq]
    exact hSum
  exact AvramDividend.Classical.causal_positive_L1_primitive_contDiff_one
    (fun t : ℝ => Real.exp (-w * t) * (β + K t)) hFull
    (AvramDividend.Classical.causal_weighted_kernel_continuous_positive
      K w β hcont)
