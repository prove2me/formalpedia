-- Prove2me | solution 1 for CohnElkies.strip_exp_abs_log_integrableOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/0aae103c-4b64-4c6d-af4b-a7a8774900a7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_abs_log_le_add_rpow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => Real.exp ((-a) * x) * |Real.log x|)
      (Ioi (0 : ℝ)) := by
  have hlinear :
      IntegrableOn (fun x : ℝ =>
        x * Real.exp ((-a) * x)) (Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hhalf :
      IntegrableOn (fun x : ℝ =>
        x ^ (-(1 / 2 : ℝ)) * Real.exp ((-a) * x))
        (Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := -(1 / 2 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hmajorant :
      IntegrableOn (fun x : ℝ =>
        x * Real.exp ((-a) * x) +
          2 * (x ^ (-(1 / 2 : ℝ)) * Real.exp ((-a) * x)))
        (Ioi (0 : ℝ)) := hlinear.add (hhalf.const_mul 2)
  have hlogcontinuous :
      ContinuousOn (fun x : ℝ => Real.log x) (Ioi (0 : ℝ)) :=
    continuousOn_id.log (fun x hx => (mem_Ioi.mp hx).ne')
  have hexpcontinuous :
      ContinuousOn (fun x : ℝ => Real.exp ((-a) * x))
        (Ioi (0 : ℝ)) := by
    fun_prop
  apply hmajorant.mono'
    ((hexpcontinuous.mul hlogcontinuous.abs).aestronglyMeasurable
      measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hlog := strip_abs_log_le_add_rpow (mem_Ioi.mp hx)
  change ‖Real.exp ((-a) * x) * |Real.log x|‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_abs]
  calc
    Real.exp ((-a) * x) * |Real.log x| ≤
        Real.exp ((-a) * x) *
          (x + 2 * x ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = x * Real.exp ((-a) * x) +
        2 * (x ^ (-(1 / 2 : ℝ)) * Real.exp ((-a) * x)) := by
      ring
end CohnElkies
