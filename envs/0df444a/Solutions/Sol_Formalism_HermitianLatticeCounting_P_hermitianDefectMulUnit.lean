-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitianDefectMulUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:51.202817+00:00
-- url     : https://prove2.me/submissions/7d079798-b4a0-4ddd-831e-44f01a4aeec0

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
theorem _root_.solution : PhiUnit := by
  intro n R _ _ _ _ S Y
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  noncomm_ring
end Formalism.HermitianLatticeCounting.P
