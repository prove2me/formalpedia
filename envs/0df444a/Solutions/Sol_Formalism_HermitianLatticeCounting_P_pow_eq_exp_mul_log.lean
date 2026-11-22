-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.pow_eq_exp_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:39.568953+00:00
-- url     : https://prove2.me/submissions/e736a44d-a920-456a-8532-aef890b8b622

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid

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
theorem _root_.solution (x : ℝ) (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp ((n:ℝ) * Real.log x) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hx, mul_comm]
end Formalism.HermitianLatticeCounting.P
