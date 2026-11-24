-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.io_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:38.544105+00:00
-- url     : https://prove2.me/submissions/5e902a40-4940-4e4e-817f-1887d564cfe5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (k : K) : (io (algebraMap K A k) : SlopeTestRemainingChoices S A) = k • (1 : SlopeTestRemainingChoices S A) := by
  unfold io
  ext u v
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd11
