-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.transfer_matrix_factorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:59:37.605028+00:00
-- url     : https://prove2.me/submissions/534b4d3a-54fe-4913-8887-165510443fdd

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.TTFactor := by
  intro K A S _ _ _ _ _ _ _ _ QQ w Y
  induction w with
  | nil => simp [TTw, Xm, Xp]
  | cons l w ih =>
    simp only [TTw, Xm, Xp]
    split_ifs
    · rw [ih]
      simp only [mul_assoc]
    · rw [ih]
      simp only [mul_assoc]
end Formalism.FourierDecayAlt.P
