-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sfac_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:35.044368+00:00
-- url     : https://prove2.me/submissions/f8469d16-ca21-4a12-8831-14eeb72d0673

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (a b : ℕ) : sfac a * sfac b ≤ sfac (a + b) := by
  unfold sfac
  rw [Finset.prod_range_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i _
  exact_mod_cast Nat.factorial_le (by omega)
end Formalism.HermitianLatticeCounting.P
