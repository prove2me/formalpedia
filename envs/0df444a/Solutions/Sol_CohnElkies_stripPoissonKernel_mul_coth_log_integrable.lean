-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_mul_coth_log_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/73680b4f-eed7-4b0d-be58-0dc984a8dc1a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_lowerCoth_log_abs_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_weighted_product_integrable

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
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T *
        Real.log (lowerCoth (Real.pi * |T| / 2))) := by
  have h := stripPoissonKernel_weighted_product_integrable
    hbelow habove lowerCoth_log_abs_integrable 0
  apply h.congr
  filter_upwards [] with T
  rw [zero_sub, stripPoissonKernel_neg]
end CohnElkies
