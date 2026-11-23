-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.diagScalar_commute_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:16.621426+00:00
-- url     : https://prove2.me/submissions/a619b6bd-5d0e-4962-a982-2b0de9b80be7

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
theorem _root_.solution {b : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : ∀ i j, Commute b (M i j)) :
    d0 b * M = M * d0 b := by
  funext i j
  simp [d0, Matrix.diagonal_mul, Matrix.mul_diagonal, (h i j).eq]
end Formalism.FourierDecayAlt.P.Wd9
