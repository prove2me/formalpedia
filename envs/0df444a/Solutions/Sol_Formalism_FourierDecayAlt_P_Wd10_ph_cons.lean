-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.ph_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:43.317762+00:00
-- url     : https://prove2.me/submissions/5639ef3b-a482-4766-a574-ff626686553d

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K S : Type} [Field K]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution (l : Letter K S) (L : List (Letter K S)) (Y : K) :
    ph (l :: L) Y = ph L Y * hp l Y := by
  simp only [ph, hp]
  split_ifs <;> rfl
end Formalism.FourierDecayAlt.P.Wd10
