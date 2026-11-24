-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hyperbolicRatioSqLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:47.050793+00:00
-- url     : https://prove2.me/submissions/82ec6038-5d45-46e4-8235-9782dcd449d1

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
theorem _root_.solution : ChShSq := by
  intro sh ch hsh hch hc
  constructor
  · intro h1
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (ch - 1), mul_le_mul h1 h1 zero_le_one hsh.le]
  · intro h1
    nlinarith [sq_nonneg (ch - 1), mul_pos hsh (sub_pos.mpr h1)]
end Formalism.HermitianLatticeCounting.P
