-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.div_pow_gainExponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:08.931896+00:00
-- url     : https://prove2.me/submissions/1dc8b256-04dc-47d4-9f8f-60525e5f2f30

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k r : ℕ) (C : ℝ) (hk : r + 2 ≤ k) (hC : 1 ≤ C) (h2 : 2 * C ^ 2 ≤ k)
    (hlog : ((r : ℝ) + 2) * Real.log k ≤ k / 6) : (C / k) ^ expo k r ≤ ((k : ℝ) ^ r)⁻¹ := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hk0 : (0:ℝ) < k := by linarith
  have hC0 : 0 < C := by linarith
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
  have hlogC : 2 * Real.log C ≤ Real.log k - Real.log 2 := by
    have h := Real.log_le_log (by positivity) (show C ^ 2 ≤ (k:ℝ) / 2 by linarith)
    rw [Real.log_pow, Real.log_div hk0.ne' (by norm_num)] at h
    push_cast at h
    linarith
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos (div_pos hC0 hk0) _) (inv_pos.mpr (pow_pos hk0 r)),
    Real.log_rpow (div_pos hC0 hk0), Real.log_inv, Real.log_pow, Real.log_div hC0.ne' hk0.ne']
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  have hcast : ((2 * r * (k - 2 - r) : ℕ) : ℝ) = 2 * r * ((k:ℝ) - 2 - r) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (show r ≤ k - 2 by omega),
      Nat.cast_sub (show 2 ≤ k by omega)]
    push_cast; try ring
  rw [hcast]
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hkr : (0:ℝ) ≤ (k:ℝ) - 2 - r := by
    have : ((r + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this; linarith
  have hx : ((r:ℝ) + 2) * Real.log 2 ≤ ((r:ℝ) + 2) * Real.log k :=
    mul_le_mul_of_nonneg_left hlk (by positivity)
  have hmain : ((r:ℝ) + 2) * Real.log k ≤ ((k:ℝ) - 2 - r) * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0.le]
  have hg0 : 0 ≤ 2 * (r:ℝ) * ((k:ℝ) - 2 - r) / k :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) hkr) hk0.le
  calc 2 * (r:ℝ) * ((k:ℝ) - 2 - r) / k * (Real.log C - Real.log k)
        ≤ 2 * (r:ℝ) * ((k:ℝ) - 2 - r) / k * ((Real.log k - Real.log 2) / 2 - Real.log k) :=
        mul_le_mul_of_nonneg_left (by linarith) hg0
    _ = -((r:ℝ) * (((k:ℝ) - 2 - r) * (Real.log k + Real.log 2))) / k := by ring
    _ ≤ -((r:ℝ) * Real.log k) := by
        rw [div_le_iff₀ hk0]
        nlinarith [mul_le_mul_of_nonneg_left hmain hr0]
end Formalism.HermitianLatticeCounting.P
