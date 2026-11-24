-- Prove2me | solution 1 for Formalism.Q3.mqk_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:42:13.367999+00:00
-- url     : https://prove2.me/submissions/ac0ba892-7815-4884-b1a8-e48be51d49d2

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
import Theorems.Thm_Formalism_Q3_mqk_sq_step
import Theorems.Thm_Formalism_Q3_mqk_finrank_two
import Theorems.Thm_Formalism_Q3_mqk_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {E : Type*} [Field E] [CharZero E]
namespace Formalism.Q3
theorem _root_.solution (F : Type*) [Field F] [Algebra F E] {k : ℕ} (a : Fin k → ℤ) (α : Fin k → E) (hα : ∀ i, α i ^ 2 = (a i : E))
    (hns : ∀ S : Finset (Fin k), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : F))) :
    ∀ T : Finset (Fin k), Module.finrank F (mqkField F α T) = 2 ^ T.card ∧
      ∀ d : F, ∀ y ∈ mqkField F α T, y ^ 2 = algebraMap F E d →
        ∃ S ⊆ T, IsSquare (d * ∏ i ∈ S, (a i : F)) := by
  intro T
  classical
  induction T using Finset.induction_on with
  | empty =>
    have hbot : mqkField F α ∅ = ⊥ := by
      simp only [mqkField, Finset.coe_empty, Set.image_empty]
      exact IntermediateField.adjoin_empty F E
    refine ⟨?_, ?_⟩
    · rw [hbot, IntermediateField.finrank_bot]
      simp
    · intro d y hy hyd
      rw [hbot, IntermediateField.mem_bot] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      have hz : z ^ 2 = d := (algebraMap F E).injective (by rw [map_pow]; exact hyd)
      exact ⟨z, by rw [Finset.prod_empty, mul_one, ← hz, sq]⟩
  | @insert j T hj ih =>
    obtain ⟨ihr, ihs⟩ := ih
    set K := mqkField F α T with hK
    have hb : (a j : E) ∈ K := by
      have := K.algebraMap_mem ((a j : ℤ) : F)
      simpa using this
    have hsq_a : ∀ z ∈ K, z ^ 2 ≠ (a j : E) := by
      intro z hz hz2
      obtain ⟨S, hS, hsq⟩ := ihs ((a j : ℤ) : F) z hz (by simpa using hz2)
      have hjS : j ∉ S := fun h => hj (hS h)
      apply hns (insert j S) (Finset.insert_nonempty j S)
      rw [Finset.prod_insert hjS]
      exact hsq
    have hβK : α j ∉ K := fun h => hsq_a (α j) h (hα j)
    have hfr := mqk_finrank_two K (α j) (a j : E) hb (hα j) hsq_a
    have hcard : (insert j T).card = T.card + 1 := by
      first
      | exact Finset.card_insert_of_not_mem hj
      | exact Finset.card_insert_of_notMem hj
    refine ⟨?_, ?_⟩
    · rw [mqk_insert, hcard, pow_succ, ← ihr, ← hfr]
      exact (Module.finrank_mul_finrank F K (IntermediateField.adjoin K {α j})).symm
    · intro d y hy hyd
      rw [mqk_insert] at hy
      have hdK : algebraMap F E d ∈ K := K.algebraMap_mem d
      rcases mqk_sq_step K (α j) (a j : E) (algebraMap F E d) hb hdK (hα j) hβK hy hyd with
        ⟨z, hz, hz2⟩ | ⟨z, hz, hz2⟩
      · obtain ⟨S, hS, hsq⟩ := ihs d z hz hz2
        exact ⟨S, hS.trans (Finset.subset_insert j T), hsq⟩
      · obtain ⟨S, hS, hsq⟩ := ihs (d * ((a j : ℤ) : F)) z hz (by rw [hz2]; simp)
        have hjS : j ∉ S := fun h => hj (hS h)
        refine ⟨insert j S, Finset.insert_subset_insert j hS, ?_⟩
        rw [Finset.prod_insert hjS, ← mul_assoc]
        exact hsq
end Formalism.Q3
