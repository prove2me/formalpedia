-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/e8cde255-0ad9-4733-98ac-edcc96a7080d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_abs_moment_integrable
import Theorems.Thm_CohnElkies_lowerRiemannLog_one_nonneg_le
import Theorems.Thm_CohnElkies_lowerRiemannLog_one_continuous

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
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * |lowerRiemannLog T 1|) := by
  have hbelow : -1 < σ := by linarith
  have hmoment := stripPoissonKernel_abs_moment_integrable
    hzero habove
  have hmajor := hmoment.const_mul (1 / 2 : ℝ)
  have hmeas :=
    (stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      lowerRiemannLog_one_continuous.abs.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with T
  have hq := lowerRiemannLog_one_nonneg_le T
  change
    ‖stripPoissonKernel σ T * |lowerRiemannLog T 1|‖ ≤
      (1 / 2 : ℝ) * (stripPoissonKernel σ T * |T|)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T),
    abs_abs, abs_of_nonneg hq.1]
  nlinarith [mul_nonneg
    (stripPoissonKernel_pos hbelow habove T).le
      (sub_nonneg.mpr hq.2)]
end CohnElkies
