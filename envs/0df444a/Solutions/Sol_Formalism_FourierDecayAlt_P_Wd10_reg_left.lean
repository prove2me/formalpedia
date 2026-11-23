-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.reg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:44.019796+00:00
-- url     : https://prove2.me/submissions/6c7f8a78-4dd6-4929-8ffa-15b58e189f05

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
theorem _root_.solution {L w : List (Letter K S)} {Y : K} (h : Reg (L ++ w) Y) : Reg L Y :=
  fun l hl => h l (List.mem_append.2 (Or.inl hl))
end Formalism.FourierDecayAlt.P.Wd10
