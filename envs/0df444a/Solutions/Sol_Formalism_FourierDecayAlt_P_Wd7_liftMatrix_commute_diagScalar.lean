-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.liftMatrix_commute_diagScalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:39.767854+00:00
-- url     : https://prove2.me/submissions/cada6a27-e011-4f3f-9303-cc442e6c4148

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
theorem _root_.solution (Q : M2 A) (b : SlopeTestRemainingChoices S A) (h : ∀ i j, Commute (io (Q i j) : SlopeTestRemainingChoices S A) b) :
    (lift0 Q : M2 (SlopeTestRemainingChoices S A)) * d0 b = d0 b * lift0 Q := by
  ext1 i j
  unfold d0 lift0
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (h i j).eq
end Formalism.FourierDecayAlt.P.Wd7
