-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_abs_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/8f70f60d-ca13-4e16-859c-0f99e3cc4a08

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_mass_mul_exponential
import Theorems.Thm_CohnElkies_stripPoissonExponentialMajorant_abs_moment_integrable

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
    Integrable (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
  have hbelow : -1 < σ := by linarith
  have hmajor :=
    stripPoissonExponentialMajorant_abs_moment_integrable.const_mul
      (stripBottomMass σ)
  have habsmeas : Measurable (fun T : ℝ => |T|) := by
    fun_prop
  apply hmajor.mono'
    ((stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      habsmeas.aestronglyMeasurable)
  filter_upwards [] with T
  change
    ‖stripPoissonKernel σ T * |T|‖ ≤
      stripBottomMass σ *
        (stripPoissonExponentialMajorant T * |T|)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T),
    abs_abs]
  calc
    stripPoissonKernel σ T * |T| ≤
      (stripBottomMass σ *
        stripPoissonExponentialMajorant T) * |T| :=
      mul_le_mul_of_nonneg_right
        (stripPoissonKernel_le_mass_mul_exponential
          hzero habove T) (abs_nonneg T)
    _ = stripBottomMass σ *
        (stripPoissonExponentialMajorant T * |T|) := by
      ring
end CohnElkies
