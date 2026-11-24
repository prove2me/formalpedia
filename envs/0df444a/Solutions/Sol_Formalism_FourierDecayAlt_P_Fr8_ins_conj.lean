-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.ins_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:21.119541+00:00
-- url     : https://prove2.me/submissions/46ce775d-0d52-4ad8-8177-d464be6df9a1

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (P Q : SlopeTestRemainingChoices S A) (hP : FreeOf a P) :
    ins a (M.map fun b => P * b * Q) = P * ins a M * Q := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at hP
  simp only [Formalism.FourierDecayAlt.Wd.ins, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Formalism.FourierDecayAlt.Wd.eU a i j * (P * M i j * Q) = Formalism.FourierDecayAlt.Wd.eU a i j * P * M i j * Q by
    simp only [mul_assoc], (hP i j).eq]
  simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Fr8
