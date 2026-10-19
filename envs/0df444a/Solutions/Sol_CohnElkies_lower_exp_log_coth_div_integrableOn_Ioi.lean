-- Prove2me | solution 1 for CohnElkies.lower_exp_log_coth_div_integrableOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/6d229c13-3b16-49a5-b373-ebe1514634a9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_exp_abs_log_div_two_integrableOn_Ioi
import Theorems.Thm_CohnElkies_lower_abs_log_coth_div_le

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
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun y : ℝ =>
        Real.exp ((-a) * y) *
          Real.log (lowerCoth (Real.pi * y / 2) / (y / 2)))
      (Ioi (0 : ℝ)) := by
  have hexponential :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hlinear :
      IntegrableOn
        (fun y : ℝ => y * Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Real.pi * (y * Real.exp ((-a) * y)) +
            |Real.log Real.pi| * Real.exp ((-a) * y) +
            2 * (Real.exp ((-a) * y) * |Real.log (y / 2)|))
        (Ioi (0 : ℝ)) :=
    ((hlinear.const_mul Real.pi).add
      (hexponential.const_mul |Real.log Real.pi|)).add
        ((lower_exp_abs_log_div_two_integrableOn_Ioi ha).const_mul 2)
  have hargument :
      ContinuousOn
        (fun y : ℝ =>
          lowerCoth (Real.pi * y / 2) / (y / 2))
        (Ioi (0 : ℝ)) := by
    unfold lowerCoth
    apply ContinuousOn.div
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro y hy
        apply Real.sinh_ne_zero.mpr
        have hypos := mem_Ioi.mp hy
        positivity
    · fun_prop
    · intro y hy
      have hypos := mem_Ioi.mp hy
      positivity
  have hargument_nonzero :
      ∀ y ∈ Ioi (0 : ℝ),
        lowerCoth (Real.pi * y / 2) / (y / 2) ≠ 0 := by
    intro y hy
    have hypos := mem_Ioi.mp hy
    unfold lowerCoth
    apply div_ne_zero
    · apply div_ne_zero
      · exact (Real.cosh_pos _).ne'
      · apply Real.sinh_ne_zero.mpr
        positivity
    · positivity
  have hcontinuous :
      ContinuousOn
        (fun y : ℝ =>
          Real.exp ((-a) * y) *
            Real.log (lowerCoth (Real.pi * y / 2) / (y / 2)))
        (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact hargument.log hargument_nonzero
  apply hmajorant.mono'
    (hcontinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos := mem_Ioi.mp hy
  have hlog :
      |Real.log (lowerCoth (Real.pi * y / 2) / (y / 2))| ≤
        Real.pi * y + |Real.log Real.pi| +
          2 * |Real.log (y / 2)| := by
    convert! lower_abs_log_coth_div_le (half_pos hypos) using 1 <;>
      ring_nf
  change
    ‖Real.exp ((-a) * y) *
      Real.log (lowerCoth (Real.pi * y / 2) / (y / 2))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp ((-a) * y) *
        |Real.log (lowerCoth (Real.pi * y / 2) / (y / 2))| ≤
      Real.exp ((-a) * y) *
        (Real.pi * y + |Real.log Real.pi| +
          2 * |Real.log (y / 2)|) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = Real.pi * (y * Real.exp ((-a) * y)) +
          |Real.log Real.pi| * Real.exp ((-a) * y) +
          2 * (Real.exp ((-a) * y) * |Real.log (y / 2)|) := by
      ring
end CohnElkies
