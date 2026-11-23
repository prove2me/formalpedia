-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.diagScalar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:47.853404+00:00
-- url     : https://prove2.me/submissions/8401314d-6b88-4c1e-a53a-7363250adcaf

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
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (c : K) (x : SlopeTestRemainingChoices S A) : d0 (c • x) = c • d0 x := by
  funext i j
  by_cases h : i = j
  · subst h
    simp [d0]
  · simp [d0, Matrix.diagonal_apply_ne _ h]
end Formalism.FourierDecayAlt.P.Wd9
