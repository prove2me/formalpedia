-- Prove2me | solution 1 for CookPvsNP.comp_conversion_return
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:44.442439+00:00
-- url     : https://prove2.me/submissions/0757d80f-f00d-4073-a461-ddcbb3844da6

import Definitions.Def_CookPvsNP_CompConversion
import Theorems.Thm_CookPvsNP_comp_cell_laws

set_option autoImplicit false
open CookPvsNP

section
variable {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
local notation "C" => compTM j₁ j₂ M₁ M₂

private theorem past (xs : List (CompCell A B))
    (hx : ∀ x ∈ xs, x.secondOrigin = false) (origin : Option (CompCell A B))
    (left right : List (Option (CompCell A B))) :
    (C).run xs.length ⟨.convReturn, (xs.map CompCell.pack ++ [origin]).tail ++ left,
      (xs.map CompCell.pack ++ [origin]).headD none, right⟩ =
      ⟨.convReturn, left, origin, (xs.map CompCell.pack).reverse ++ right⟩ := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hx₁ : ∀ a ∈ xs, a.secondOrigin = false := fun a ha => hx a (by simp [ha])
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs (L R : List (Option (CompCell A B))) :
        (C).step ⟨.convReturn, L, CompCell.pack x, R⟩ =
          ⟨.convReturn, L.tail, L.headD none, CompCell.pack x :: R⟩ := by
      cases L <;> simp [TM.step, TM.IsHalting, compTM, (comp_cell_laws j₁ j₂).1, hx₀]
    rw [hs]
    cases xs <;> simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih hx₁ (CompCell.pack x :: right)

private theorem finish (a : Option A) (b : Option B)
    (left : List (Option (CompCell A B))) (r : Option (CompCell A B))
    (rs : List (Option (CompCell A B))) (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run 2 ⟨.convReturn, left, CompCell.originSymbol a b, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, r :: rs⟩ := by
  simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
    CompCell.originSymbol, CompCell.unpack, CompCell.plain]
  exact hr

private theorem return_raw (xs : List (CompCell A B))
    (hx : ∀ x ∈ xs, x.secondOrigin = false) (a : Option A) (b : Option B)
    (left : List (Option (CompCell A B))) (r : Option (CompCell A B))
    (rs : List (Option (CompCell A B))) (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run (xs.length + 2)
      ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
        (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by
  have hp := past j₁ j₂ M₁ M₂ xs hx (CompCell.originSymbol a b) left (r :: rs)
  have hf : (C).run 2
      ⟨.convReturn, left, CompCell.originSymbol a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by
    rw [← List.map_reverse]
    cases xs.reverse with
    | nil => exact finish j₁ j₂ M₁ M₂ a b left r rs hr
    | cons x rest =>
      exact finish j₁ j₂ M₁ M₂ a b left (CompCell.pack x)
        (rest.map CompCell.pack ++ r :: rs) (by rw [(comp_cell_laws j₁ j₂).1])
  rw [Nat.add_comm]
  unfold TM.run at hp hf ⊢
  dsimp only [compTM] at hp hf ⊢
  rw [Function.iterate_add_apply, hp]
  exact hf

end

/-- The conversion return scan reaches its marked origin and starts the second machine. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (xs : List (CompCell A B)) (hx : ∀ x ∈ xs, x.secondOrigin = false)
    (a : Option A) (b : Option B) (left : List (Option (CompCell A B)))
    (r : Option (CompCell A B)) (rs : List (Option (CompCell A B)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (compTM j₁ j₂ M₁ M₂).run (xs.length + 2)
      ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
        (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by
  exact return_raw j₁ j₂ M₁ M₂ xs hx a b left r rs hr

#print axioms solution
