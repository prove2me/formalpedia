-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitianDefectAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:32.215639+00:00
-- url     : https://prove2.me/submissions/5811e1e3-ba8c-4e55-a99c-47033ad00cd7

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
theorem _root_.solution : PhiDiff := by
  intro n R _ _ _ _ S Y Z hS
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose, hS]
  noncomm_ring
end Formalism.HermitianLatticeCounting.P
