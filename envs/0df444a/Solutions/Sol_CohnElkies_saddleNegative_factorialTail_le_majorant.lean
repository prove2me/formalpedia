-- Prove2me | solution 1 for CohnElkies.saddleNegative_factorialTail_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/8363e92e-4b89-4ac1-a592-ef886d830e57

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleExpSeries_term_le_exp_mul_half_pow
import Theorems.Thm_CohnElkies_saddleNegativeTruncation_half_pow_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {C ℓ y : ℝ}
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
      (y ^ saddleSmallResidueTruncation ℓ /
        ((saddleSmallResidueTruncation ℓ).factorial : ℝ)) ≤
      2 * saddleSmallResidueTailMajorant C ℓ := by
  let N : ℕ := saddleSmallResidueTruncation ℓ
  have hterm := saddleExpSeries_term_le_exp_mul_half_pow hy N
  have hgeo := saddleNegativeTruncation_half_pow_le ℓ
  change Real.exp y * (y ^ N / (N.factorial : ℝ)) ≤ _
  calc
    Real.exp y * (y ^ N / (N.factorial : ℝ)) ≤
      Real.exp y *
        (Real.exp (2 * y) * (1 / 2 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
    _ = Real.exp (3 * y) * (1 / 2 : ℝ) ^ N := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp (3 * (Real.log ℓ / 8 + C)) *
        (2 * Real.exp (-10 * Real.log ℓ)) := by
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr (by linarith)
      · exact hgeo
      · positivity
      · positivity
    _ = 2 * saddleSmallResidueTailMajorant C ℓ := by
      unfold saddleSmallResidueTailMajorant
      calc
        Real.exp (3 * (Real.log ℓ / 8 + C)) *
            (2 * Real.exp (-10 * Real.log ℓ)) =
          2 *
            (Real.exp (3 * (Real.log ℓ / 8 + C)) *
              Real.exp (-10 * Real.log ℓ)) := by ring
        _ = 2 *
            Real.exp
              (3 * (Real.log ℓ / 8 + C) +
                (-10 * Real.log ℓ)) := by
          rw [← Real.exp_add]
        _ = 2 *
            Real.exp
              (3 * C - (77 / 8 : ℝ) * Real.log ℓ) := by
          congr 2
          ring
end CohnElkies
