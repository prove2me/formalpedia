-- Prove2me | solution 1 for BarelyTestable.LowerBound.characterizations
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:52:29.366289+00:00
-- url     : https://prove2.me/submissions/c7e7a779-872f-4b2b-aff2-be3c6c612a4f

import Definitions.Def_BarelyTestable_LowerBound_Cube
open BarelyTestable.LowerBound NonmonotoneSubmod.Shared
namespace Submod722
variable {α : Type} [Fintype α] [DecidableEq α] {f : Oracle α}

theorem squares (hf : Submodular f) : NonnegativeSquares f := by
  intro S u v h
  obtain ⟨huv,hu,hv⟩ := h
  have h1 : insert u S ∪ insert v S = insert u (insert v S) := by ext; simp <;> tauto
  have h2 : insert u S ∩ insert v S = S := by ext; simp; grind
  have hh := hf (insert u S) (insert v S)
  rw [h1,h2] at hh
  unfold slack
  linarith

theorem marginal (hs : NonnegativeSquares f) : DiminishingReturns f := by
  intro S T u hst hu
  have aux (D : Finset α) (hd : u ∉ S ∪ D) :
      f (insert u (S ∪ D)) - f (S ∪ D) ≤ f (insert u S) - f S := by
    induction D using Finset.induction_on with
    | empty => simp
    | @insert a D ha ih =>
      rw [Finset.union_insert] at hd ⊢
      have hu' : u ∉ S ∪ D := by grind
      by_cases ha' : a ∈ S ∪ D
      · simpa [Finset.insert_eq_of_mem ha'] using ih hu'
      · have hx := hs (S ∪ D) u a ⟨by grind,hu',ha'⟩
        unfold slack at hx
        linarith [ih hu']
  simpa [Finset.union_eq_right.mpr hst] using aux T (by simpa [Finset.union_eq_right.mpr hst] using hu)

theorem global (hd : DiminishingReturns f) : Submodular f := by
  have aux (S T D : Finset α) (hst : S ⊆ T) (hdis : Disjoint D T) :
      f (T ∪ D) - f T ≤ f (S ∪ D) - f S := by
    induction D using Finset.induction_on with
    | empty => simp
    | @insert a D ha ih =>
      rw [Finset.disjoint_insert_left] at hdis
      have h := hd (S ∪ D) (T ∪ D) (u := a) (Finset.union_subset_union_left hst)
        (by simp [hdis.1,ha])
      rw [Finset.union_insert, Finset.union_insert]
      linarith [ih hdis.2]
  intro A B
  have h := aux (A ∩ B) A (B \ A) Finset.inter_subset_left (Finset.disjoint_left.mpr (fun x hx h => (Finset.mem_sdiff.mp hx).2 h))
  have h1 : A ∪ (B \ A) = A ∪ B := by ext; simp <;> tauto
  have h2 : (A ∩ B) ∪ (B \ A) = B := by ext; simp <;> tauto
  rw [h1,h2] at h
  linarith

end Submod722
open BarelyTestable.LowerBound NonmonotoneSubmod.Shared

theorem solution {n : ℕ} (f : Oracle (Fin n)) :
    (Submodular f ↔ NonnegativeSquares f) ∧
    (Submodular f ↔ DiminishingReturns f) :=
  ⟨⟨Submod722.squares, fun h => Submod722.global (Submod722.marginal h)⟩,
   ⟨fun h => Submod722.marginal (Submod722.squares h), Submod722.global⟩⟩

#print axioms solution
