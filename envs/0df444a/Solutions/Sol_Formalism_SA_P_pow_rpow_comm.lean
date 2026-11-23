-- Prove2me | solution 1 for Formalism.SA.P.pow_rpow_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:34.622196+00:00
-- url     : https://prove2.me/submissions/aa91df46-4db3-4c2f-9cc6-3e77ab84e5d2

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (t y : ℝ) (ht : 0 < t) (n : ℕ) : (t ^ n) ^ y = (t ^ y) ^ n := by
  rw [← Real.rpow_natCast (t ^ y), ← Real.rpow_natCast t, ← Real.rpow_mul ht.le,
    ← Real.rpow_mul ht.le, mul_comm]
end Formalism.SA.P
