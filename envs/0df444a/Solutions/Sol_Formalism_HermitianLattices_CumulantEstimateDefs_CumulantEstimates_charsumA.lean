-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.charsumA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:35.467448+00:00
-- url     : https://prove2.me/submissions/a7d93a11-6c1b-4d53-a6c4-f226d436d124

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
theorem _root_.solution (n : ℕ) [NeZero n] (t : ZMod n) :
    ∑ b : ZMod n, (ZMod.stdAddChar (b * t) : ℂ) = if t = 0 then (n : ℂ) else 0 := by
  rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar n), ZMod.card]
  split_ifs <;> simp
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
