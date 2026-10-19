-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_scaled_riemann_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/57e0b37b-b7bc-45af-a8c7-8b2394c17e81

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_riemann_le

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
    {d : ℕ} (hd : 2 ≤ d) {c T : ℝ}
    (hc : 0 < c) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hR : 0 < c * Real.sqrt d :=
    mul_pos hc (Real.sqrt_pos.mpr hdreal)
  have hratio :
      Real.pi * (c * Real.sqrt d) ^ 2 /
          ((d : ℝ) / 2) = 2 * Real.pi * c ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hdreal.le]
    field_simp [hdreal.ne']
  have hconstant :
      Real.log (2 * Real.pi * c ^ 2) + 1 =
        Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) := by
    have hfactor :
        2 * Real.pi * Real.exp 1 * c ^ 2 =
          (2 * Real.pi * c ^ 2) * Real.exp 1 := by
      ring
    rw [hfactor,
      Real.log_mul (show 2 * Real.pi * c ^ 2 ≠ 0 by positivity)
        (Real.exp_ne_zero _), Real.log_exp]
  have h := lowerGammaBoundaryLog_dimension_riemann_le
    hd hR hT
  rw [hratio] at h
  calc
    lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * c ^ 2) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := h
    _ = ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
      rw [← hconstant]
end CohnElkies
