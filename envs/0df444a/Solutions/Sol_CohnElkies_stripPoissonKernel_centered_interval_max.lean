-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_centered_interval_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/e55ca0c0-4b21-4354-bb50-d8e124c0d798

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_intervalIntegral_stripPoissonKernel
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_centered_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    (∫ x in Icc (s - r) (s + r), stripPoissonKernel σ x) ≤
      ∫ x in Icc (-r) r, stripPoissonKernel σ x := by
  rw [integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : s - r ≤ s + r),
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    intervalIntegral_stripPoissonKernel hbelow habove,
    intervalIntegral_stripPoissonKernel hbelow habove]
  exact stripPoissonPrimitive_centered_le hbelow habove hr s
end CohnElkies
