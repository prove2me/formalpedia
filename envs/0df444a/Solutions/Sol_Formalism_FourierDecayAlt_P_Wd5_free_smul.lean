-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.free_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:35.913475+00:00
-- url     : https://prove2.me/submissions/a032c0e4-28f4-4e88-b9b2-a1001f43ed5e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution {c : S} {b : SlopeTestRemainingChoices S A} (k : K) (h : FreeOf c b) : FreeOf c (k • b) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * (k • b) = (k • b) * eU c i j
  rw [Matrix.mul_smul, Matrix.smul_mul, (h i j).eq]
end Formalism.FourierDecayAlt.P.Wd5
