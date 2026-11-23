-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:15.765275+00:00
-- url     : https://prove2.me/submissions/f2bb8a87-d937-4a71-8a4c-d6a601bc85e3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BudgetLiftBounds
namespace Formalism.FourierDecayAlt.P.BudgetLiftBounds
theorem _root_.solution {E : Type} [AddCommGroup E] [DecidableEq E] (L : AddSubgroup E) (S : Finset E) :
    ∃ R : Finset E, (∀ t ∈ S, ∃ t0 ∈ R, t - t0 ∈ L) ∧ (∀ x ∈ R, ∀ y ∈ R, x - y ∈ L → x = y) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S _ ih =>
    obtain ⟨R, h1, h2⟩ := ih
    by_cases h : ∃ t0 ∈ R, a - t0 ∈ L
    · refine ⟨R, ?_, h2⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact h
      · exact h1 t ht
    · refine ⟨insert a R, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ⟨t, Finset.mem_insert_self _ _, by simp⟩
        · obtain ⟨t0, ht0, h3⟩ := h1 t ht
          exact ⟨t0, Finset.mem_insert_of_mem ht0, h3⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxa | hxR
        · rcases Finset.mem_insert.mp hy with hya | hyR
          · rw [hxa, hya]
          · exact absurd ⟨y, hyR, hxa ▸ hxy⟩ h
        · rcases Finset.mem_insert.mp hy with hya | hyR
          · exact absurd ⟨x, hxR, by have := L.neg_mem hxy; rw [hya] at this; simpa using this⟩ h
          · exact h2 x hxR y hyR hxy
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
