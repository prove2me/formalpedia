-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.diag_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:43.908199+00:00
-- url     : https://prove2.me/submissions/8a68bf04-443b-4f63-92ad-84d1744732cd

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P.Fr5
section Core
variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]
end Core
section Slots
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
private lemma d0_eq_diagonal (b : SlopeTestRemainingChoices S A) : d0 b = !![b, 0; 0, b] := by
  first
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> rfl)
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> simp [d0])
end Slots
section Level
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
end Level
section Main
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
end Main
end Formalism.FourierDecayAlt.P.Fr5
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (p1 p2 w c1 c2 e1 e2 : SlopeTestRemainingChoices S A) :
    !![p1, 0; 0, p2] * d0 w * !![c1, 0; 0, c2] * !![e1, 0; 0, e2] =
      !![p1 * w * c1 * e1, 0; 0, p2 * w * c2 * e2] := by
  first
  | (simp only [d0_eq_diagonal, Matrix.mul_fin_two, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      mul_assoc]; done)
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;>
       simp [d0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, mul_assoc])
end Formalism.FourierDecayAlt.P.Fr5
