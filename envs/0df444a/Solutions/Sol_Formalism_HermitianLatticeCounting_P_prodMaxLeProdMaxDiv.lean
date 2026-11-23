-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodMaxLeProdMaxDiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:40.250336+00:00
-- url     : https://prove2.me/submissions/8749fdb9-d4a3-4550-9859-af2f9ce5e4ad

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
theorem _root_.solution : PThreshold := by
  intro ι _ x H hH hx
  have hH0 : 0 < H := by linarith
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro v _; exact zero_le_one.trans (le_max_left _ _)
  · intro v _
    have e : H * (x v / H) = x v := by field_simp
    rw [mul_max_of_nonneg _ _ hH0.le, mul_one, e]
    exact max_le_max hH le_rfl
end Formalism.HermitianLatticeCounting.P
