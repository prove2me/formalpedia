-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minLeSqrtMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:45.377922+00:00
-- url     : https://prove2.me/submissions/a4a6971e-98ca-4a7e-a16e-4b70f909bf92

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
theorem _root_.solution : MinGeom := by
  intro a b ha hb
  have hm : 0 ≤ min a b := le_min ha hb
  have h2 : min a b ^ 2 ≤ a * b := by
    rw [sq]; exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm ha
  calc min a b = Real.sqrt (min a b ^ 2) := (Real.sqrt_sq hm).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt h2
end Formalism.HermitianLatticeCounting.P
