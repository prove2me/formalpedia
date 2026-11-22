-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.free_io
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:48.159775+00:00
-- url     : https://prove2.me/submissions/c52cef75-b32d-4e88-b5ac-93c76168f458

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
private lemma mul_scalar_comm_of_entries_zero_or_one {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A) (x : A)
    (hM : ∀ k l, M k l = 0 ∨ M k l = 1) : M * Matrix.scalar n x = Matrix.scalar n x * M := by
  ext k l
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases hM k l with h | h <;> rw [h] <;> simp
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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  exact mul_scalar_comm_of_entries_zero_or_one (eU a i j) x (fun k l => by
    first
    | (simp only [eU, Matrix.of_apply]; split_ifs <;> simp)
    | (rw [eU]; simp only [Matrix.of_apply]; split_ifs <;> simp))
end Formalism.FourierDecayAlt.P.Fr5
