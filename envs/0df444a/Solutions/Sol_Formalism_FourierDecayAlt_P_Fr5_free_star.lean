-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.free_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:25.462806+00:00
-- url     : https://prove2.me/submissions/b4672f9d-73af-42e7-a6c6-7603e6dd6768

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
private lemma star_eU_eq_eU_swap (a : S) (i j : Fin 2) : star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  have key : ∀ k l : Ix S, star ((eU a i j : SlopeTestRemainingChoices S A) l k) = (eU a j i : SlopeTestRemainingChoices S A) k l := by
    intro k l
    simp only [eU, Matrix.of_apply]
    by_cases h1 : l a = i ∧ k a = j ∧ ∀ b, b ≠ a → l b = k b
    · have h2 : k a = j ∧ l a = i ∧ ∀ b, b ≠ a → k b = l b :=
        ⟨h1.2.1, h1.1, fun b hb => (h1.2.2 b hb).symm⟩
      rw [if_pos h1, if_pos h2, star_one]
    · have h2 : ¬ (k a = j ∧ l a = i ∧ ∀ b, b ≠ a → k b = l b) :=
        fun h => h1 ⟨h.2.1, h.1, fun b hb => (h.2.2 b hb).symm⟩
      rw [if_neg h1, if_neg h2, star_zero]
  exact Matrix.ext key
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
theorem _root_.solution {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (star x) := by
  intro i j
  have e1 : star (eU a j i : SlopeTestRemainingChoices S A) = eU a i j := star_eU_eq_eU_swap a j i
  first
  | (have h3 := (hx j i).star_star
     rw [e1] at h3
     exact h3)
  | (show eU a i j * star x = star x * eU a i j
     rw [← e1, ← star_mul, ← star_mul, (hx j i).eq])
end Formalism.FourierDecayAlt.P.Fr5
