-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitianDefectComposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:00:56.706806+00:00
-- url     : https://prove2.me/submissions/43bc4bf1-b44c-4f5f-b833-96411f0bc183

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
theorem _root_.solution : PhiProduct := by
  intro n R _ _ _ _ S Y Y' hS
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose, hS]
  noncomm_ring
end Formalism.HermitianLatticeCounting.P
