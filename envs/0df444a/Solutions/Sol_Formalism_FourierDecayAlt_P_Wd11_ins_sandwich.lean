-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.ins_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:14:11.305792+00:00
-- url     : https://prove2.me/submissions/9fbaaee8-a960-4ad9-ba1b-51c13c9377f1

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_mul_diagScalar_apply

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (M : M2 (SlopeTestRemainingChoices S A)) (y : SlopeTestRemainingChoices S A) :
    ins a (d0 x * M * d0 y) = x * ins a M * y := by
  unfold ins
  simp only [mul_diagScalar_apply, diagScalar_mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, (hx i j).eq]
  simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Wd11
