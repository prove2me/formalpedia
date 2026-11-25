-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.oneLeProdInfinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:01.32746+00:00
-- url     : https://prove2.me/submissions/2b5bbf07-1816-4040-ad87-039df6323187

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
theorem _root_.solution : IntegerProductGeOne := by
  intro E _ _ a ha
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have : (1:ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs h
  exact_mod_cast this
end Formalism.HermitianLatticeCounting.P
