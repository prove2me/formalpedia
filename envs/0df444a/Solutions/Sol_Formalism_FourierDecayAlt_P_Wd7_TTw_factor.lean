-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.TTw_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:58.191855+00:00
-- url     : https://prove2.me/submissions/4a221f69-4033-44f1-bafa-6a06c8733077

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (Y : K) :
    TTw QQ w Y = Xm w Y * lift0 (QQ Y) * Xp w Y := by
  induction w with
  | nil => simp [TTw, Xm, Xp]
  | cons l w ih => by_cases h : l.plus <;> simp [TTw, Xm, Xp, h, ih, mul_assoc]
end Formalism.FourierDecayAlt.P.Wd7
