-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.factIneq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:42.225344+00:00
-- url     : https://prove2.me/submissions/5128abbd-5cff-4a47-b515-2be59458b1ea

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
open scoped Nat
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution (n : ℕ) : 6 ^ n * n ! ≤ (2 * n + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1 + 1),
      Nat.factorial_succ (2 * n + 1), Nat.factorial_succ n, pow_succ]
    have h1 : 6 * (n + 1) * (6 ^ n * n !) ≤ 6 * (n + 1) * (2 * n + 1)! := Nat.mul_le_mul le_rfl ih
    have h2 : 6 * (n + 1) ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1) := by nlinarith
    have h3 := Nat.mul_le_mul h2 (le_refl (2 * n + 1)!)
    calc 6 ^ n * 6 * ((n + 1) * n !) = 6 * (n + 1) * (6 ^ n * n !) := by ring
      _ ≤ 6 * (n + 1) * (2 * n + 1)! := h1
      _ ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1) * (2 * n + 1)! := h3
      _ = (2 * n + 1 + 1 + 1) * ((2 * n + 1 + 1) * (2 * n + 1)!) := by ring
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
