-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_integer_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/ed03efe9-debf-4aa9-a258-1863e77a1b1f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer
import Theorems.Thm_CohnElkies_lower_exp_log_sqrtFactor_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) (k : ℕ) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog (k : ℝ) R y) := by
  have hconstant :
      Integrable
        (fun y : ℝ =>
          ((k : ℝ) * Real.log (Real.pi * R ^ 2)) *
            Real.exp ((-a) * |y|)) :=
    (strip_exp_abs_integrable ha).const_mul
      ((k : ℝ) * Real.log (Real.pi * R ^ 2))
  have hsum :
      Integrable
        (fun y : ℝ =>
          ∑ j ∈ Finset.range k,
            Real.exp ((-a) * |y|) *
              Real.log
                (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2))) := by
    exact integrable_finsetSum (Finset.range k)
      (fun j _ => lower_exp_log_sqrtFactor_integrable ha
        (Nat.cast_nonneg j))
  have hmodel :
      Integrable
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) *
            ((k : ℝ) * Real.log (Real.pi * R ^ 2) -
              ∑ j ∈ Finset.range k,
                Real.log
                  (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)))) := by
    simpa only [mul_sub, Finset.mul_sum, mul_comm] using!
      hconstant.sub hsum
  refine hmodel.congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  rw [lowerGammaBoundaryLog_integer k R hy]
end CohnElkies
