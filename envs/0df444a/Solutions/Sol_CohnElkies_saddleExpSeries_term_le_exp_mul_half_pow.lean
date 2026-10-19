-- Prove2me | solution 1 for CohnElkies.saddleExpSeries_term_le_exp_mul_half_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/e4a5062b-04ca-4dc8-9940-cec7298e695f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleExpSeries_hasSum

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
    {y : ℝ} (hy : 0 ≤ y) (m : ℕ) :
    y ^ m / (m.factorial : ℝ) ≤
      Real.exp (2 * y) * (1 / 2 : ℝ) ^ m := by
  have hterm :
      (2 * y) ^ m / (m.factorial : ℝ) ≤
        Real.exp (2 * y) := by
    simpa using!
      (sum_le_hasSum ({m} : Finset ℕ)
        (fun n hn => by positivity)
        (saddleExpSeries_hasSum (2 * y)))
  have hpower :
      (2 * y) ^ m * (1 / 2 : ℝ) ^ m = y ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    y ^ m / (m.factorial : ℝ) =
        ((2 * y) ^ m / (m.factorial : ℝ)) *
          (1 / 2 : ℝ) ^ m := by
      rw [div_mul_eq_mul_div, hpower]
    _ ≤ Real.exp (2 * y) * (1 / 2 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hterm (by positivity)
end CohnElkies
