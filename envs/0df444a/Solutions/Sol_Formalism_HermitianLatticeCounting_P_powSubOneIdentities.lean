-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.powSubOneIdentities
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:40.298691+00:00
-- url     : https://prove2.me/submissions/9bf64608-f781-43f0-9635-f72e2703e8d8

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
theorem _root_.solution : PowSubOneIdentities := by
  intro T k f hT hk
  have hT1 : (1:ℝ) < T := by exact_mod_cast (by omega : 1 < T)
  have hTk : (0:ℝ) < (T:ℝ) ^ k := by positivity
  constructor
  · rw [mul_comm f k, pow_mul, ← mul_pow, mul_sub, mul_one, mul_inv_cancel₀ hTk.ne']
  · have key : (T:ℝ) ^ (k - 1) ≤ ((T:ℝ) ^ k - 1) / ((T:ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      have e : (T:ℝ) ^ k = (T:ℝ) ^ (k - 1) * T := by
        rw [← pow_succ]; congr 1; omega
      rw [e]
      nlinarith [one_le_pow₀ hT1.le (n := k - 1)]
    rw [← pow_mul, mul_comm f (k - 1), pow_mul]
    exact pow_le_pow_left₀ (by positivity) key f
end Formalism.HermitianLatticeCounting.P
