-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.factorialPiWeight_le_pi_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:14.689495+00:00
-- url     : https://prove2.me/submissions/23a0ddb7-172f-4022-af31-6ede871e1273

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
theorem _root_.solution (v : ℝ) (hv : 1 ≤ v) (j t : ℕ) : s5bA v j ≤ Real.pi ^ t * s5bA v (j + t) := by
  unfold s5bA
  have hπ := Real.pi_pos
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hf : ((j - 1).factorial : ℝ) ≤ ((j + t - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show j - 1 ≤ j + t - 1 by omega)
  have hvp : v ^ j ≤ v ^ (j + t) := pow_le_pow_right₀ hv (by omega)
  have e1 : (v / Real.pi) ^ j = v ^ j / Real.pi ^ j := div_pow _ _ _
  have e2 : Real.pi ^ t * (((j + t - 1).factorial : ℝ) * (v / Real.pi) ^ (j + t)) =
      ((j + t - 1).factorial : ℝ) * v ^ (j + t) / Real.pi ^ j := by
    rw [eq_div_iff (pow_ne_zero j hπ0), div_pow, pow_add Real.pi j t]
    calc _ = ((j + t - 1).factorial : ℝ) * v ^ (j + t) *
          ((Real.pi ^ j * Real.pi ^ t) / (Real.pi ^ j * Real.pi ^ t)) := by ring
      _ = ((j + t - 1).factorial : ℝ) * v ^ (j + t) := by rw [div_self (by positivity), mul_one]
  rw [e1, e2, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hf hvp (by positivity) (by positivity)
end Formalism.HermitianLatticeCounting.P
