-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.choose_succ_mul_two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.143338+00:00
-- url     : https://prove2.me/submissions/516743d9-f741-41f5-8818-cf5b2c03172e

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.BranchingDeterminantCap
private theorem two_pow_le_succ_factorial (j : ℕ) : 2 ^ j ≤ (j + 1).factorial := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ]
    calc 2 ^ k * 2 ≤ (k + 1).factorial * (k + 1 + 1) := Nat.mul_le_mul ih (by omega)
      _ = (k + 1 + 1) * (k + 1).factorial := Nat.mul_comm _ _
end Formalism.BranchingDeterminantCap
end

set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (r j : ℕ) : r.choose (j + 1) * 2 ^ j ≤ r ^ (j + 1) := by
  calc r.choose (j + 1) * 2 ^ j ≤ r.choose (j + 1) * (j + 1).factorial :=
        Nat.mul_le_mul le_rfl (two_pow_le_succ_factorial j)
    _ = r.descFactorial (j + 1) := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
    _ ≤ r ^ (j + 1) := Nat.descFactorial_le_pow r (j + 1)
end Formalism.BranchingDeterminantCap
