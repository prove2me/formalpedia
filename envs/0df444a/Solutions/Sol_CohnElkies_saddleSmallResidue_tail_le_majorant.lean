-- Prove2me | solution 1 for CohnElkies.saddleSmallResidue_tail_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/3a21920b-f2ab-416a-b869-89668532cc47

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleExpSeries_term_le_exp_mul_half_pow
import Theorems.Thm_CohnElkies_saddleSmallResidueTruncation_half_pow_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {C ℓ y : ℝ}
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
        (y ^ (saddleSmallResidueTruncation ℓ + 1) /
          ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) ≤
      saddleSmallResidueTailMajorant C ℓ := by
  let m : ℕ := saddleSmallResidueTruncation ℓ + 1
  have hterm := saddleExpSeries_term_le_exp_mul_half_pow
    hy m
  have hgeo := saddleSmallResidueTruncation_half_pow_le ℓ
  change Real.exp y *
      (y ^ m / (m.factorial : ℝ)) ≤ _
  calc
    Real.exp y * (y ^ m / (m.factorial : ℝ)) ≤
        Real.exp y *
          (Real.exp (2 * y) * (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
    _ = Real.exp (3 * y) * (1 / 2 : ℝ) ^ m := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp
          (3 * (Real.log ℓ / 8 + C)) *
        Real.exp (-10 * Real.log ℓ) := by
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr (by linarith)
      · exact hgeo
      · positivity
      · positivity
    _ = saddleSmallResidueTailMajorant C ℓ := by
      rw [← Real.exp_add]
      unfold saddleSmallResidueTailMajorant
      congr 1
      ring
end CohnElkies
