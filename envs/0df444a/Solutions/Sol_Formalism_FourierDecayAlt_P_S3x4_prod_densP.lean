-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.prod_densP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.23622+00:00
-- url     : https://prove2.me/submissions/c9171cf6-f8d8-40e0-8dcc-0488dba3f598

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_densityProduct_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution (q : ℕ) (hq : 0 < q) (m : ℕ) (hi : ℤ) (hm : (m : ℤ) ≤ hi) (k : ℕ) (hk : k ≤ m) :
    ((∏ j ∈ range k, (q ^ m - q ^ j) : ℕ) : ℝ) * densP 1 q ((m : ℤ) + 1) hi =
      (q : ℝ) ^ (m * k) * densP 1 q ((m : ℤ) - k + 1) hi := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    rw [Finset.prod_range_succ, Nat.cast_mul, mul_right_comm, ih',
      densityProduct_step q ((m : ℤ) - (k + 1 : ℕ) + 1) hi (by push_cast; omega)]
    have e1 : ((m : ℤ) - (k + 1 : ℕ) + 1 + 1) = (m : ℤ) - k + 1 := by push_cast; ring
    rw [e1, Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
    have e2 : (q : ℝ) ^ (-((m : ℤ) - (k + 1 : ℕ) + 1)) = (q : ℝ) ^ k / (q : ℝ) ^ m := by
      have : -((m : ℤ) - (k + 1 : ℕ) + 1) = (k : ℤ) - m := by push_cast; ring
      rw [this, zpow_sub₀ hq', zpow_natCast, zpow_natCast]
    rw [e2]
    push_cast
    have hm0 : (q : ℝ) ^ m ≠ 0 := pow_ne_zero _ hq'
    rw [Nat.mul_succ, pow_add]
    field_simp
end Formalism.FourierDecayAlt.P.S3x4
