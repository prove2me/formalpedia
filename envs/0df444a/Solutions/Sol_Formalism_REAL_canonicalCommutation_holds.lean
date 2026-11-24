-- Prove2me | solution 1 for Formalism.REAL.canonicalCommutation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:41.205804+00:00
-- url     : https://prove2.me/submissions/293bb647-d815-4f19-aef9-45ba016bda2a

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_deriv_mulX_commutator
import Theorems.Thm_Formalism_REAL_mulX_negDeriv_commutator
import Theorems.Thm_Formalism_REAL_deriv_mul_deriv_comm
import Theorems.Thm_Formalism_REAL_mulX_mul_mulX_comm
import Theorems.Thm_Formalism_REAL_deriv_mul_mulX_comm_of_ne

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
theorem _root_.solution : CCR := by
  intro M n' ε ε' i j a b
  have hI : (if (i, a) = (j, b) then 1 else 0 : Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ)) =
      if i = j ∧ a = b then 1 else 0 := by
    by_cases hh : i = j ∧ a = b
    · obtain ⟨rfl, rfl⟩ := hh
      simp
    · rw [if_neg hh, if_neg]
      intro he
      exact hh (Prod.mk.inj he)
  simp only [bop, bpl]
  by_cases h1 : sgnv ε ε' i a = true <;> by_cases h2 : sgnv ε ε' j b = true
  · simp only [if_pos h1, if_pos h2]
    exact ⟨(deriv_mulX_commutator _ _).trans hI, deriv_mul_deriv_comm _ _, mulX_mul_mulX_comm _ _⟩
  · have hne : (i, a) ≠ (j, b) := by
      intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h2 h1
    have hnd : ¬(i = j ∧ a = b) := fun hh => hne (by rw [hh.1, hh.2])
    simp only [if_pos h1, if_neg h2]
    refine ⟨?_, deriv_mul_mulX_comm_of_ne hne, ?_⟩
    · rw [if_neg hnd, mul_neg, neg_mul, deriv_mul_deriv_comm (i, a) (j, b), sub_self]
    · rw [mul_neg, neg_mul, deriv_mul_mulX_comm_of_ne hne.symm]
  · have hne : (i, a) ≠ (j, b) := by
      intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h1 h2
    have hnd : ¬(i = j ∧ a = b) := fun hh => hne (by rw [hh.1, hh.2])
    simp only [if_neg h1, if_pos h2]
    refine ⟨?_, (deriv_mul_mulX_comm_of_ne hne.symm).symm, ?_⟩
    · rw [if_neg hnd, mulX_mul_mulX_comm (i, a) (j, b), sub_self]
    · rw [neg_mul, mul_neg, deriv_mul_mulX_comm_of_ne hne]
  · simp only [if_neg h1, if_neg h2]
    refine ⟨(mulX_negDeriv_commutator _ _).trans hI, mulX_mul_mulX_comm _ _, ?_⟩
    rw [neg_mul_neg, neg_mul_neg, deriv_mul_deriv_comm (i, a) (j, b)]
end Formalism.REAL
