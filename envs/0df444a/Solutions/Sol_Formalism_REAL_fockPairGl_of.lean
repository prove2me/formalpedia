-- Prove2me | solution 1 for Formalism.REAL.fockPairGl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:29.391435+00:00
-- url     : https://prove2.me/submissions/df282d9c-79f5-4dd7-805c-4fd5f0fb956c

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_satisfiesGlRelations_bilinearLeft
import Theorems.Thm_Formalism_REAL_bilinearRight_commutator
import Theorems.Thm_Formalism_REAL_bilinearLeft_mul_bilinearRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (h : CCR) : FockPairGl := by
  intro M n' ε ε'
  have hBP : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (h M n' ε ε' i j a b).1
  have hBB : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (h M n' ε ε' i j a b).2.1
  have hPP : ∀ i j a b, bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a :=
    fun i j a b => (h M n' ε ε' i j a b).2.2
  have hEg : Eg ε ε' = bilinearLeft (bop ε ε') (bpl ε ε') := by
    funext i j
    rfl
  have hEg' : Eg' ε ε' = fun a b => -bilinearRight (bop ε ε') (bpl ε ε') a b := by
    funext a b
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hEg]
    exact satisfiesGlRelations_bilinearLeft hBP hBB hPP
  · rw [hEg']
    intro a b c d
    simp only [neg_mul_neg]
    rw [bilinearRight_commutator hBP hBB hPP a b c d]
    simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
    split_ifs <;> abel
  · intro i j a b
    rw [hEg, hEg']
    simp only [mul_neg, neg_mul]
    rw [bilinearLeft_mul_bilinearRight hBP hBB hPP]
end Formalism.REAL
