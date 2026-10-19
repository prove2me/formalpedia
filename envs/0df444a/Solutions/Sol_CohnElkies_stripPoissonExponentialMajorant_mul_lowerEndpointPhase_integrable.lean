-- Prove2me | solution 1 for CohnElkies.stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/b66b16c5-3973-40bb-ba72-3db6c0e1974e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_lowerEndpointPhase_continuous
import Theorems.Thm_CohnElkies_abs_lowerEndpointPhase_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable
      (fun T : ℝ =>
        stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖) := by
  have ha : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hfirst :
      Integrable
        (fun T : ℝ =>
          ((Real.pi / 2) * Real.pi) *
            (|T| ^ (1 : ℕ) *
              Real.exp (-(Real.pi / 2) * |T|))) :=
    (integrable_abs_pow_mul_exp_neg_mul_abs 1 ha).const_mul
      ((Real.pi / 2) * Real.pi)
  have hsecond :
      Integrable
        (fun T : ℝ =>
          (Real.pi / 2) *
            (|T| ^ (2 : ℕ) *
              Real.exp (-(Real.pi / 2) * |T|))) :=
    (integrable_abs_pow_mul_exp_neg_mul_abs 2 ha).const_mul
      (Real.pi / 2)
  apply (hfirst.add hsecond).mono'
    (by
      unfold stripPoissonExponentialMajorant
      exact
        ((continuous_const.mul
          (Real.continuous_exp.comp
            (continuous_const.mul continuous_abs))).mul
          lowerEndpointPhase_continuous.norm).aestronglyMeasurable)
  filter_upwards [] with T
  have hphase := abs_lowerEndpointPhase_le T
  have hfactor :
      0 ≤ (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * |T|) := by positivity
  change
    |((Real.pi / 2) * Real.exp (-(Real.pi / 2) * |T|)) *
        ‖lowerEndpointPhase T‖| ≤
      ((Real.pi / 2) * Real.pi) *
          (|T| ^ (1 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|)) +
        (Real.pi / 2) *
          (|T| ^ (2 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|))
  rw [abs_of_nonneg (mul_nonneg hfactor (norm_nonneg _))]
  calc
    (Real.pi / 2) * Real.exp (-(Real.pi / 2) * |T|) *
        ‖lowerEndpointPhase T‖ ≤
      ((Real.pi / 2) * Real.exp (-(Real.pi / 2) * |T|)) *
        (Real.pi * |T| + T ^ 2) := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hphase hfactor
    _ = ((Real.pi / 2) * Real.pi) *
          (|T| ^ (1 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|)) +
        (Real.pi / 2) *
          (|T| ^ (2 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|)) := by
          rw [pow_one, sq_abs]
          ring
end CohnElkies
