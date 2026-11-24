-- Prove2me | solution 1 for FairSelling.exists_value_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:31.784792+00:00
-- url     : https://prove2.me/submissions/f90182cc-0536-461f-858b-a3fa48ab8210

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (v : G → ℝ) (hv : ∀ g, 0 ≤ v g) :
    ∀ (A : Finset G) (T : ℝ), (∑ g ∈ A, p g) ≤ T → T ≤ ∑ g ∈ A, max (p g) (v g) →
    ∃ w : G → ℝ, (∀ g, 0 ≤ w g) ∧ (∀ g, w g ≤ v g) ∧ (∀ g ∉ A, w g = v g) ∧
      ∑ g ∈ A, max (p g) (w g) = T := by
  classical
  intro A
  induction A using Finset.induction with
  | empty =>
    intro T h1 h2
    simp only [Finset.sum_empty] at h1 h2
    exact ⟨v, hv, fun g => le_refl _, fun g _ => rfl, by simp; linarith⟩
  | @insert a s ha IH =>
    intro T h1 h2
    rw [Finset.sum_insert ha] at h1 h2
    by_cases hcase : (∑ g ∈ s, p g) + max (p a) (v a) ≤ T
    · obtain ⟨w, hw0, hwv, hwout, hwsum⟩ := IH (T - max (p a) (v a)) (by linarith) (by linarith)
      refine ⟨w, hw0, hwv, fun g hg => hwout g (fun h => hg (Finset.mem_insert_of_mem h)), ?_⟩
      rw [Finset.sum_insert ha, hwout a ha, hwsum]
      ring
    · push_neg at hcase
      obtain ⟨w, hw0, hwv, hwout, hwsum⟩ := IH (∑ g ∈ s, p g) (le_refl _)
        (Finset.sum_le_sum (fun g _ => le_max_left _ _))
      set c : ℝ := T - ∑ g ∈ s, p g with hc
      have hca : p a ≤ c := by simp only [hc]; linarith
      have hclt : c < max (p a) (v a) := by simp only [hc]; linarith
      have hcv : c ≤ v a := by
        rcases max_cases (p a) (v a) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hclt <;> linarith
      refine ⟨Function.update w a c, ?_, ?_, ?_, ?_⟩
      · intro g
        by_cases hg : g = a
        · subst hg; simpa using le_trans (hp g) hca
        · simpa [Function.update_of_ne hg] using hw0 g
      · intro g
        by_cases hg : g = a
        · subst hg; simpa using hcv
        · simpa [Function.update_of_ne hg] using hwv g
      · intro g hg
        have hga : g ≠ a := by rintro rfl; exact hg (Finset.mem_insert_self g s)
        rw [Function.update_of_ne hga]
        exact hwout g (fun h => hg (Finset.mem_insert_of_mem h))
      · rw [Finset.sum_insert ha]
        have hupd : ∑ g ∈ s, max (p g) (Function.update w a c g)
            = ∑ g ∈ s, max (p g) (w g) :=
          Finset.sum_congr rfl (fun g hg => by
            rw [Function.update_of_ne (by rintro rfl; exact ha hg)])
        rw [hupd, hwsum]
        simp only [Function.update_self]
        rw [max_eq_right hca, hc]
        ring
end FairSelling
