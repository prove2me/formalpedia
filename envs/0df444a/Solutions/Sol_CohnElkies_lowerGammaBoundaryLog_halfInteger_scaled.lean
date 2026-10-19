-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/bae84c0e-49e4-4e6c-ab9d-dc5c721764af

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_pos
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger
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
    (k : ℕ) {ℓ R T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ℓ R (ℓ * T) =
      ℓ * Real.log (Real.pi * R ^ 2 / ℓ) -
        ∑ j ∈ Finset.range k,
          lowerRiemannLog T (((j : ℝ) + 1 / 2) / ℓ) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * ℓ * |T| / 2)) -
        (1 / 2 : ℝ) * Real.log (|T| / 2) := by
  have hℓ : 0 < ℓ := by
    rw [hℓeq]
    positivity
  have hy : ℓ * T ≠ 0 :=
    mul_ne_zero hℓ.ne' hT
  have hraw := lowerGammaBoundaryLog_halfInteger
    k R hy
  rw [← hℓeq] at hraw
  rw [hraw]
  have hterm (j : ℕ) :
      Real.log
        (Real.sqrt
          (((j : ℝ) + 1 / 2) ^ 2 + (ℓ * T / 2) ^ 2)) =
        Real.log ℓ +
          lowerRiemannLog T (((j : ℝ) + 1 / 2) / ℓ) := by
    rw [lowerRiemannLog_scaled_factor hℓ]
    have hrad :
        0 < (((j : ℝ) + 1 / 2) / ℓ) ^ 2 + T ^ 2 / 4 := by
      nlinarith [sq_nonneg (((j : ℝ) + 1 / 2) / ℓ),
        sq_pos_of_ne_zero hT]
    rw [Real.log_mul hℓ.ne'
      (Real.sqrt_pos.mpr hrad).ne']
    rfl
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ _j ∈ Finset.range k, Real.log ℓ) =
        (k : ℝ) * Real.log ℓ := by
    simp
  rw [hsum]
  have habs : |ℓ * T| = ℓ * |T| := by
    rw [abs_mul, abs_of_pos hℓ]
  rw [habs]
  have harg :
      Real.pi * (ℓ * |T|) / 2 =
        Real.pi * ℓ * |T| / 2 := by ring
  rw [harg]
  have ht : 0 < |T| / 2 := by positivity
  have hcoth :
      0 < lowerCoth (Real.pi * ℓ * |T| / 2) := by
    apply lowerCoth_pos
    positivity
  have hden : ℓ * |T| / 2 = ℓ * (|T| / 2) := by ring
  rw [hden, Real.log_div hcoth.ne'
    (mul_ne_zero hℓ.ne' ht.ne'),
    Real.log_mul hℓ.ne' ht.ne']
  rw [Real.log_div
    (show Real.pi * R ^ 2 ≠ 0 by positivity) hℓ.ne']
  rw [hℓeq]
  ring
end CohnElkies
