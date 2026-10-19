-- Prove2me | solution 1 for CohnElkies.harmonic_stripPoissonKernel_zero_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/fcb39c9f-c0ba-4030-ac8a-38e74398f5ae

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_exponentialMajorant_of_nonneg
import Theorems.Thm_CohnElkies_harmonic_stripPoissonExponentialMajorant_abs_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable
      (fun T : ℝ => stripPoissonKernel 0 T * |T|) := by
  have hmajor :=
    harmonic_stripPoissonExponentialMajorant_abs_integrable
  have hmeas : Measurable
      (fun T : ℝ => stripPoissonKernel 0 T * |T|) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with T
  have hkernel :=
    stripPoissonKernel_le_exponentialMajorant_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) < 1) T
  have hpos := stripPoissonKernel_pos
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1) T
  have hmajorpos : 0 ≤ stripPoissonExponentialMajorant T := by
    unfold stripPoissonExponentialMajorant
    positivity
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hpos.le (abs_nonneg T))]
  exact mul_le_mul_of_nonneg_right
    hkernel (abs_nonneg T)
end CohnElkies
