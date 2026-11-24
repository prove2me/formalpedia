-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.tTFactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:33.784164+00:00
-- url     : https://prove2.me/submissions/c7f36c20-b4d8-4097-abca-5bde89745741

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution : TTFactor := by
  intro K A S _ _ _ _ _ _ _ _ QQ w Y
  induction w with
  | nil => simp [TTw, Xm, Xp]
  | cons l w ih =>
    by_cases h : l.plus = true
    · simp [TTw, Xm, Xp, h, ih, mul_assoc]
    · simp [TTw, Xm, Xp, h, ih, mul_assoc]
end Formalism.FourierDecayAlt.P.Wd8
