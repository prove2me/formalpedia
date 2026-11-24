-- Prove2me | solution 1 for Combinatorics.Line.exists_map_eq_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:31.3348+00:00
-- url     : https://prove2.me/submissions/0ea37f8e-1b5f-4716-a568-d0cedafa47cc

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Pigeonhole
public import Definitions.Def_ShelahHalesJewett_Line

set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
variable {η α ι ι' κ : Type*}
open Combinatorics.Line
namespace Combinatorics.Line
theorem _root_.solution [Finite κ] {N : ℕ} (hN : Nat.card κ ≤ N) (a b : α)
    (C : (Fin N → α) → κ) : ∃ l : Line α (Fin N), C (l a) = C (l b) := by
  cases nonempty_fintype κ
  let u (j : Fin (N + 1)) (p : Fin N) : α := if (p : ℕ) < j then a else b
  obtain ⟨j, j', hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun j ↦ C (u j))
    (by simpa [Nat.card_eq_fintype_card] using Nat.lt_succ_of_le hN)
  wlog hlt : (j : ℕ) < j' generalizing j j'
  · exact this j' j hne.symm h.symm (by grind)
  let l : Line α (Fin N) :=
    ⟨fun p ↦ if (p : ℕ) < j then some a else if (p : ℕ) < j' then none else some b,
      ⟨⟨j, by grind⟩, by simp [hlt]⟩⟩
  refine ⟨l, ?_⟩
  convert h.symm using 2 <;> ext p <;> grind [coe_apply]
end Combinatorics.Line
