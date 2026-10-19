-- Prove2me | solution 1 for CohnElkies.lowerRiemannErrorMajorant_poisson_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/1ea53000-2ac7-4d25-8fee-6cb2cddc9530

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_mul_abs_lowerRiemannLog_zero_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_mul_coth_log_integrable

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
      stripPoissonKernel σ T *
        lowerRiemannErrorMajorant T) := by
  have hbelow : -1 < σ := by linarith
  have hqzero :=
    (stripPoissonKernel_mul_abs_lowerRiemannLog_zero_integrable
      hbelow habove).const_mul (3 : ℝ)
  have hone :=
    (stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
      hzero habove).const_mul (2 : ℝ)
  have hcoth :=
    (stripPoissonKernel_mul_coth_log_integrable
      hbelow habove).const_mul (1 / 2 : ℝ)
  have hsum := hqzero.add (hone.add hcoth)
  convert! hsum using 1
  ext T
  change
    stripPoissonKernel σ T * lowerRiemannErrorMajorant T =
      3 * (stripPoissonKernel σ T * |lowerRiemannLog T 0|) +
        (2 * (stripPoissonKernel σ T * |lowerRiemannLog T 1|) +
          (1 / 2 : ℝ) *
            (stripPoissonKernel σ T *
              Real.log (lowerCoth (Real.pi * |T| / 2))))
  unfold lowerRiemannErrorMajorant
  ring
end CohnElkies
