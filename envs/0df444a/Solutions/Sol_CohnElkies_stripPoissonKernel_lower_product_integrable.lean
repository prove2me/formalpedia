-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_lower_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/dac43690-d8fc-478a-aed3-7ad5e573119d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_center_of_lower

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hbase : Integrable (fun T : ℝ =>
      stripPoissonKernel 0 T * g T)) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * g T) := by
  let C : ℝ := 1 / (1 - Real.cos (stripAngle σ))
  have hangle := stripAngle_mem_Ioo hbelow
    (show σ < 1 by linarith)
  have hqlt : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle.2.le hangle.1
    simpa using! h
  have hC : 0 < C := by
    try dsimp [C]
    exact one_div_pos.mpr (by linarith)
  have hmajor : Integrable
      (fun T : ℝ => C *
        ‖stripPoissonKernel 0 T * g T‖) :=
    hbase.norm.const_mul C
  have hmeas : Measurable
      (fun T : ℝ => stripPoissonKernel σ T * g T) := by
    have hk : Measurable
        (fun T : ℝ => stripPoissonKernel σ T) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    exact hk.mul hg.measurable
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with T
  have hσpositive := stripPoissonKernel_pos
    hbelow (show σ < 1 by linarith) T
  have hzero := stripPoissonKernel_pos
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1) T
  have hkernel := stripPoissonKernel_le_center_of_lower
    hbelow hnonpos T
  calc
    ‖stripPoissonKernel σ T * g T‖ =
        stripPoissonKernel σ T * ‖g T‖ := by
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos hσpositive]
    _ ≤ (C * stripPoissonKernel 0 T) * ‖g T‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact hkernel
    _ = C * ‖stripPoissonKernel 0 T * g T‖ := by
      rw [norm_mul, Real.norm_of_nonneg hzero.le]
      ring
end CohnElkies
