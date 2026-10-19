-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_shifted_centered_interval_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/107e7c94-39c7-4629-8680-60bd1c6061fc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_stripPoissonKernel_centered_interval_max

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    (∫ x in Icc (-r) r,
      stripPoissonKernel σ (s - x)) ≤
      ∫ x in Icc (-r) r,
        stripPoissonKernel σ (0 - x) := by
  have hleft :
      (∫ x in Icc (-r) r,
        stripPoissonKernel σ (s - x)) =
        ∫ x in Icc (s - r) (s + r),
          stripPoissonKernel σ x := by
    rw [integral_Icc_eq_integral_Ioc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
      ← intervalIntegral.integral_of_le
        (by linarith : s - r ≤ s + r),
      intervalIntegral.integral_comp_sub_left]
    congr 1; ring
  have hright :
      (∫ x in Icc (-r) r,
        stripPoissonKernel σ (0 - x)) =
        ∫ x in Icc (-r) r,
          stripPoissonKernel σ x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simpa using! stripPoissonKernel_neg σ x
  rw [hleft, hright]
  exact stripPoissonKernel_centered_interval_max
    hbelow habove hr s
end CohnElkies
