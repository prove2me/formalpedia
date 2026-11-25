-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.rpowMulRpowNegLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:01:44.26673+00:00
-- url     : https://prove2.me/submissions/8d905846-9ffb-4bc2-be06-28e232d5de2c

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
theorem _root_.solution : SizeCancel := by
  intro sz e q hsz hq
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hsz (by linarith)
end Formalism.HermitianLatticeCounting.P
