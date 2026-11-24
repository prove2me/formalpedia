-- Prove2me | solution 1 for FairSelling.fill_exists_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:05.452996+00:00
-- url     : https://prove2.me/submissions/58aab575-3298-4222-a855-b0dbaa15f095

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
import Theorems.Thm_FairSelling_fillout_snoc
import Theorems.Thm_FairSelling_fill_one
import Theorems.Thm_FairSelling_fill_exists

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (t m : ℕ) (A C S : Finset G) (d r : ℝ) (f₀ : Option G),
      (∀ g ∈ A, ε ≤ vbar w p g) → (∀ g ∈ A, vbar w p g ≤ 2 * ε) →
      (∀ g ∈ C, vbar w p g ≤ ε) →
      (∀ g ∈ S, ε ≤ p g) → (∀ g ∈ S, vbar w p g = p g) →
      Disjoint A C → Disjoint A S → Disjoint C S →
      0 ≤ d → (r = 0 ∨ ε ≤ r) →
      (∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f) →
      (f₀ = none → r = 0) →
      A.card ≤ m + 1 + t → (A.card = m + 1 + t ∨ (S = ∅ ∧ r = 0)) →
      (m : ℝ) * (3 * ε) + 2 * ε + (t : ℝ) * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r →
      Nonempty (FillOut w p ε (m + 1) (A ∪ C ∪ S) d r f₀) := by
  classical
  intro t
  induction t with
  | zero =>
    intro m A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n hcard hseed hbud
    exact fill_exists w p hp hε m A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n
      (by omega) (by simpa using hseed) (by push_cast at hbud ⊢; linarith)
  | succ t ih =>
    intro m A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n hcard hseed hbud
    have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
    have hbud' : (m : ℝ) * (3 * ε) + 2 * ε + (t : ℝ) * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r := by
      push_cast at hbud
      nlinarith
    by_cases hm : m = 0
    · subst hm
      refine fill_one w p hp hε A C S d r f₀ hS2 hAC hAS hCS hd hr hf₀ hf₀n ?_
      push_cast at hbud
      nlinarith [Nat.cast_nonneg (α := ℝ) t]
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      by_cases hA2card : 2 ≤ A.card
      · -- pair up two large goods into one pure part
        obtain ⟨e₁, he₁⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨e₂, he₂⟩ : (A.erase e₁).Nonempty := by
          refine Finset.card_pos.mp ?_
          rw [Finset.card_erase_of_mem he₁]; omega
        have he₂A : e₂ ∈ A := Finset.mem_of_mem_erase he₂
        have hne : e₂ ≠ e₁ := Finset.ne_of_mem_erase he₂
        set A' : Finset G := (A.erase e₁).erase e₂ with hA'def
        have hA'card : A'.card = A.card - 2 := by
          rw [hA'def, Finset.card_erase_of_mem he₂, Finset.card_erase_of_mem he₁]
          omega
        have hAsum : (∑ g ∈ A, vbar w p g)
            = vbar w p e₁ + vbar w p e₂ + ∑ g ∈ A', vbar w p g := by
          rw [hA'def, show vbar w p e₁ + vbar w p e₂
                + ∑ g ∈ (A.erase e₁).erase e₂, vbar w p g
              = vbar w p e₁ + (vbar w p e₂ + ∑ g ∈ (A.erase e₁).erase e₂, vbar w p g) from by ring,
            Finset.add_sum_erase _ _ he₂, Finset.add_sum_erase _ _ he₁]
        have hrec := ih m A' C S d r f₀
          (fun g hg => hA1 g (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
          (fun g hg => hA2 g (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
          hC1 hS1 hS2
          (Finset.disjoint_of_subset_left
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hAC)
          (Finset.disjoint_of_subset_left
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hAS)
          hCS hd hr
          (fun f hf => ⟨fun hc => (hf₀ f hf).1
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)),
            (hf₀ f hf).2.1, (hf₀ f hf).2.2.1, (hf₀ f hf).2.2.2.1, (hf₀ f hf).2.2.2.2⟩)
          hf₀n (by omega)
          (by
            rcases hseed with h | h
            · left; omega
            · right; exact h)
          (by
            have h1 : vbar w p e₁ ≤ 2 * ε := hA2 e₁ he₁
            have h2 : vbar w p e₂ ≤ 2 * ε := hA2 e₂ he₂A
            rw [hAsum] at hbud
            push_cast at hbud ⊢
            linarith)
        obtain ⟨F⟩ := hrec
        refine fillout_snoc w p ε F ?_ (fun f hf => Finset.mem_union_right _ (by simp [hf]))
          {e₁, e₂} none 0 0 ?_ ?_ le_rfl le_rfl (by linarith) ?_ (Or.inl rfl)
          (fun h => absurd rfl h) (fun h => absurd rfl h) (fun _ => rfl)
          (fun f hf => absurd hf (by simp)) ?_
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
          · exact Finset.mem_union_right _ hx
        · intro x hx
          have hxe : x = e₁ ∨ x = e₂ := by simpa using hx
          rcases hxe with rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ he₁)
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ he₂A)
        · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          have hxe : x = e₁ ∨ x = e₂ := by simpa using hx
          have hxA : x ∈ A := by rcases hxe with rfl | rfl; exacts [he₁, he₂A]
          simp only [Option.toFinset_none, Finset.union_empty] at hx'
          rcases Finset.mem_union.mp hx' with hx' | hx'
          · rcases Finset.mem_union.mp hx' with hx' | hx'
            · rcases Finset.mem_union.mp hx' with hx' | hx'
              · rcases hxe with rfl | rfl
                · exact (Finset.notMem_erase _ _) (Finset.mem_of_mem_erase hx')
                · exact (Finset.notMem_erase _ _) hx'
              · exact Finset.disjoint_left.mp hAC hxA hx'
            · exact Finset.disjoint_left.mp hAS hxA hx'
          · exact (hf₀ x (Option.mem_toFinset.mp hx')).1 hxA
        · have h1 : ε ≤ vbar w p e₁ := hA1 e₁ he₁
          have h2 : ε ≤ vbar w p e₂ := hA1 e₂ he₂A
          have hpair : vbarSum w p {e₁, e₂} = vbar w p e₁ + vbar w p e₂ := by
            simp [vbarSum, Finset.sum_pair (Ne.symm hne)]
          rw [hpair]
          linarith
        · intro f
          simp only [reduceCtorEq, if_false, zero_add]
          by_cases hmem : f ∈ F.sell
          · rw [if_pos hmem]
          · rw [if_neg hmem]
            split
            · exact hr0
            · exact hp f
      · -- fewer than two large goods: no pairing is needed
        refine ih (m + 1) A C S d r f₀ hA1 hA2 hC1 hS1 hS2 hAC hAS hCS hd hr hf₀ hf₀n
          (by omega) ?_ hbud'
        rcases hseed with h | h
        · omega
        · exact Or.inr h
end FairSelling
