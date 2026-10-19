-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_integer_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/8a9f3ebd-9018-4a16-88d7-3a638b7858e7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer
import Theorems.Thm_CohnElkies_lowerRiemannLog_scaled_factor

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
    {k : ℕ} (hk : 0 < k) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R ((k : ℝ) * T) =
      (k : ℝ) * Real.log (Real.pi * R ^ 2 / (k : ℝ)) -
        ∑ j ∈ Finset.range k,
          lowerRiemannLog T ((j : ℝ) / (k : ℝ)) := by
  have hkreal : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hy : (k : ℝ) * T ≠ 0 :=
    mul_ne_zero hkreal.ne' hT
  rw [lowerGammaBoundaryLog_integer k R hy]
  have hterm (j : ℕ) :
      Real.log
        (Real.sqrt
          ((j : ℝ) ^ 2 + (((k : ℝ) * T) / 2) ^ 2)) =
        Real.log (k : ℝ) +
          lowerRiemannLog T ((j : ℝ) / (k : ℝ)) := by
    rw [lowerRiemannLog_scaled_factor hkreal]
    have hrad :
        0 < ((j : ℝ) / (k : ℝ)) ^ 2 + T ^ 2 / 4 := by
      nlinarith [sq_nonneg ((j : ℝ) / (k : ℝ)),
        sq_pos_of_ne_zero hT]
    rw [Real.log_mul hkreal.ne'
      (Real.sqrt_pos.mpr hrad).ne']
    rfl
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ _j ∈ Finset.range k, Real.log (k : ℝ)) =
        (k : ℝ) * Real.log (k : ℝ) := by
    simp
  rw [hsum]
  rw [Real.log_div
    (show Real.pi * R ^ 2 ≠ 0 by positivity) hkreal.ne']
  simp only [div_eq_mul_inv]
  ring
end CohnElkies
