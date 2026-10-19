-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/394effb4-0ac7-4ccd-ac07-30eb30c49c0c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_integrable
import Theorems.Thm_CohnElkies_lower_exp_log_sqrtFactor_integrable
import Theorems.Thm_CohnElkies_lower_exp_log_coth_div_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger

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
        lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y) := by
  have hconstant :
      Integrable
        (fun y : ℝ =>
          (((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2)) *
            Real.exp ((-a) * |y|)) :=
    (strip_exp_abs_integrable ha).const_mul
      (((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2))
  have hsum :
      Integrable
        (fun y : ℝ =>
          ∑ j ∈ Finset.range k,
            Real.exp ((-a) * |y|) *
              Real.log
                (Real.sqrt
                  (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) := by
    exact integrable_finsetSum (Finset.range k)
      (fun j _ => lower_exp_log_sqrtFactor_integrable ha
        (by have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith))
  have hcorrection :
      Integrable
        (fun y : ℝ =>
          (1 / 2 : ℝ) *
            (Real.exp ((-a) * |y|) *
              Real.log
                (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)))) :=
    (lower_exp_log_coth_div_integrable ha).const_mul (1 / 2)
  have hbase := (hconstant.sub hsum).add hcorrection
  refine hbase.congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  change
    ((((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2)) *
      Real.exp ((-a) * |y|) -
        ∑ j ∈ Finset.range k,
          Real.exp ((-a) * |y|) *
            Real.log
              (Real.sqrt
                (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) +
      (1 / 2 : ℝ) *
        (Real.exp ((-a) * |y|) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))) =
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y
  rw [lowerGammaBoundaryLog_halfInteger k R hy]
  simp only [mul_add, mul_sub, Finset.mul_sum]
  ring
end CohnElkies
