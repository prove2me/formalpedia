-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_mul_lowerEndpointPhase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/f15ffc8a-d20d-4cac-827e-83204778ae78

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_lowerEndpointPhase_continuous
import Theorems.Thm_CohnElkies_stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_le_mass_mul_exponential

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
      stripPoissonKernel σ T * lowerEndpointPhase T) := by
  have hbelow : -1 < σ := by linarith
  have hmajor :=
    stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable.const_mul
      (stripBottomMass σ)
  have hmeas :=
    (stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      lowerEndpointPhase_continuous.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with T
  change
    ‖stripPoissonKernel σ T * lowerEndpointPhase T‖ ≤
      stripBottomMass σ *
        (stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T)]
  calc
    stripPoissonKernel σ T * ‖lowerEndpointPhase T‖ ≤
      (stripBottomMass σ *
        stripPoissonExponentialMajorant T) *
          ‖lowerEndpointPhase T‖ :=
      mul_le_mul_of_nonneg_right
        (stripPoissonKernel_le_mass_mul_exponential
          hzero habove T) (norm_nonneg _)
    _ = stripBottomMass σ *
        (stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖) := by ring
end CohnElkies
