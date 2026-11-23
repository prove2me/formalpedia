-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.alg_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:47.982365+00:00
-- url     : https://prove2.me/submissions/73b59386-322f-43ff-b8e9-c532f17f04fa

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (c : K) (M : M2 (SlopeTestRemainingChoices S A)) : algebraMap K (SlopeTestRemainingChoices S A) c • M = c • M := by
  funext i j
  simp [Algebra.smul_def]
end Formalism.FourierDecayAlt.P.Wd9
