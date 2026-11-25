-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitianDefectConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:38.166411+00:00
-- url     : https://prove2.me/submissions/d10ee991-f3d2-47e3-a894-4d1f10d49722

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
theorem _root_.solution : PhiGram := by
  intro n R _ _ _ _ S Y hS
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hS]
  noncomm_ring
end Formalism.HermitianLatticeCounting.P
