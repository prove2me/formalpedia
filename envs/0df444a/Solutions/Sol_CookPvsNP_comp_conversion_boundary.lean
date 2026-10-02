-- Prove2me | solution 1 for CookPvsNP.comp_conversion_boundary
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:29:31.623413+00:00
-- url     : https://prove2.me/submissions/27185bb6-88a6-489a-b7fd-8c8628e02572

import Theorems.Thm_CookPvsNP_comp_conversion_return
import Theorems.Thm_CookPvsNP_comp_conversion_seek
import Theorems.Thm_CookPvsNP_comp_cell_laws

set_option autoImplicit false
open CookPvsNP

section
variable {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
local notation "C" => compTM j₁ j₂ M₁ M₂

private theorem boundary_raw (xs : List (CompCell A B))
    (hx : ∀ x ∈ xs, x.secondOrigin = false) (a : Option A) (b : Option B)
    (left : List (Option (CompCell A B))) (padding : ℕ) (empty : Bool) :
    (C).run (xs.length + 2 * padding + 3)
      ⟨if empty then .convEmptyRight else .convCopy false,
        xs.map CompCell.pack ++ CompCell.originSymbol a b :: left,
        (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
        (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b,
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate padding none⟩ := by
  let rb : CompCell A B := ⟨none, none, false, false, true, false, false⟩
  have hrb : CompCell.pack rb = CompCell.rightMarker := by
    simp [rb, CompCell.pack, CompCell.rightMarker, CompCell.blank]
  have hblank : CompCell.pack (CompCell.blank : CompCell A B) = none := rfl
  cases padding with
  | zero =>
    have hs : (C).run 1
        ⟨if empty then .convEmptyRight else .convCopy false,
          xs.map CompCell.pack ++ CompCell.originSymbol a b :: left, CompCell.rightMarker, []⟩ =
        ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
          (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, [CompCell.rightMarker]⟩ := by
      cases empty <;> cases xs <;> simp [TM.run, TM.step, TM.IsHalting, compTM,
        CompCell.rightMarker, CompCell.unpack, CompCell.pack, CompCell.blank]
    have hf := comp_conversion_return j₁ j₂ M₁ M₂ xs hx a b left CompCell.rightMarker []
      (by rw [← hrb, (comp_cell_laws j₁ j₂).1])
    simp only [List.replicate_zero, List.nil_append, List.headD_cons, List.tail_cons,
      Nat.mul_zero, Nat.add_zero] at *
    rw [show xs.length + 3 = (xs.length + 2) + 1 by omega]
    unfold TM.run at hs hf ⊢
    dsimp only [compTM] at hs hf ⊢
    rw [Function.iterate_add_apply, hs]
    exact hf
  | succ n =>
    let ys := List.replicate n (CompCell.blank : CompCell A B) ++ rb :: xs
    have hy : ∀ y ∈ ys, y.secondOrigin = false := by
      intro y h
      simp only [ys, List.mem_append, List.mem_replicate, List.mem_cons] at h
      rcases h with ⟨_, rfl⟩ | rfl | h
      · rfl
      · rfl
      · exact hx y h
    have hm : ys.map CompCell.pack = List.replicate n none ++ CompCell.rightMarker :: xs.map CompCell.pack := by
      simp [ys, hrb, hblank]
    have hs : (C).run 1
        ⟨if empty then .convEmptyRight else .convCopy false,
          xs.map CompCell.pack ++ CompCell.originSymbol a b :: left, none,
          List.replicate n none ++ [CompCell.rightMarker]⟩ =
        ⟨.convSeekOldRight, CompCell.rightMarker :: (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left),
          (List.replicate n none ++ [CompCell.rightMarker]).headD none,
          (List.replicate n none ++ [CompCell.rightMarker]).tail⟩ := by
      cases empty <;> simp [TM.run, TM.step, TM.IsHalting, compTM, CompCell.unpack,
        CompCell.pack, CompCell.blank, CompCell.rightMarker]
    have hk := comp_conversion_seek j₁ j₂ M₁ M₂ n
      (CompCell.rightMarker :: (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left))
    have hf := comp_conversion_return j₁ j₂ M₁ M₂ ys hy a b left none [] rfl
    have ht : (List.replicate n (none : Option (CompCell A B)) ++ CompCell.rightMarker ::
          (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left)).tail =
        (ys.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left := by
      rw [hm]
      cases n <;> simp [List.replicate_succ, List.append_assoc]
    have hh : (List.replicate n (none : Option (CompCell A B)) ++ CompCell.rightMarker ::
          (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left)).headD none =
        (ys.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none := by
      rw [hm]
      cases n <;> simp [List.replicate_succ]
    rw [ht, hh] at hk
    have hlen : ys.length = n + 1 + xs.length := by simp [ys]; omega
    have hout : (ys.map CompCell.pack).reverse ++ [none] =
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate (n + 1) none := by
      simp [hm, List.reverse_append, List.append_assoc, List.replicate_succ']
    rw [hout] at hf
    simp only [List.replicate_succ, List.cons_append, List.headD_cons, List.tail_cons]
    rw [show xs.length + 2 * (n + 1) + 3 = (ys.length + 2) + ((n + 1) + 1) by omega]
    unfold TM.run at hs hk hf ⊢
    dsimp only [compTM] at hs hk hf ⊢
    rw [Function.iterate_add_apply _ (ys.length + 2) ((n + 1) + 1),
      Function.iterate_add_apply _ (n + 1) 1, hs, hk]
    simpa only [List.replicate_succ] using hf

end

/-- Conversion relocates the right boundary, clears the old one, and returns to the second origin. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (xs : List (CompCell A B)) (hx : ∀ x ∈ xs, x.secondOrigin = false)
    (a : Option A) (b : Option B) (left : List (Option (CompCell A B)))
    (padding : ℕ) (empty : Bool) :
    (compTM j₁ j₂ M₁ M₂).run (xs.length + 2 * padding + 3)
      ⟨if empty then .convEmptyRight else .convCopy false,
        xs.map CompCell.pack ++ CompCell.originSymbol a b :: left,
        (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
        (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b,
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate padding none⟩ := by
  exact boundary_raw j₁ j₂ M₁ M₂ xs hx a b left padding empty

#print axioms solution
