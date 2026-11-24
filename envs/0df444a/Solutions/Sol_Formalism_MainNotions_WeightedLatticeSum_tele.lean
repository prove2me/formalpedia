-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:39.118973+00:00
-- url     : https://prove2.me/submissions/bd269d0d-6cbc-4068-8612-52babd34b656

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.WeightedLatticeSum
open Finset
private theorem inv_mul_le_two_mul_inv_sub_inv_of_sq (k a b : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ha2 : a ^ 2 = k)
    (hb2 : b ^ 2 = k - 1) : 1 / (k * a) ≤ 2 * (1 / b - 1 / a) := by
  have hba : b ≤ a := by nlinarith
  have hab : (a - b) * (a + b) = 1 := by linear_combination ha2 - hb2
  have hD : 0 < a * b * (a + b) := mul_pos (mul_pos ha0 hb0) (add_pos ha0 hb0)
  have e : 2 * (1 / b - 1 / a) = 2 / (a * b * (a + b)) := by
    apply eq_div_of_mul_eq hD.ne'
    calc 2 * (1 / b - 1 / a) * (a * b * (a + b))
        = 2 * ((1 / b * b) * a - (1 / a * a) * b) * (a + b) := by ring
      _ = 2 * (a - b) * (a + b) := by
          rw [one_div_mul_cancel hb0.ne', one_div_mul_cancel ha0.ne']; ring
      _ = 2 := by rw [mul_assoc, hab, mul_one]
  have hk0 : 0 < k := by nlinarith
  rw [e, div_le_div_iff₀ (mul_pos hk0 ha0) hD, ← ha2]
  nlinarith [mul_le_mul_of_nonneg_left hba (sq_nonneg a),
    mul_le_mul_of_nonneg_left (mul_le_mul hba hba hb0.le ha0.le) ha0.le]
end Formalism.MainNotions.WeightedLatticeSum
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (k : ℝ) (hk : 2 ≤ k) :
    1 / (k * Real.sqrt k) ≤ 2 * (1 / Real.sqrt (k - 1) - 1 / Real.sqrt k) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  exact inv_mul_le_two_mul_inv_sub_inv_of_sq k _ _ (Real.sqrt_pos.mpr hk0) (Real.sqrt_pos.mpr hk1) (Real.sq_sqrt hk0.le)
    (Real.sq_sqrt hk1.le)
end Formalism.MainNotions.WeightedLatticeSum
