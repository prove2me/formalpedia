-- Prove2me | solution 1 for BandParity.sum_sign_mul_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:58.276445+00:00
-- url     : https://prove2.me/submissions/ac368be9-f5ef-4288-a355-eb83f1431ee8

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
public import Theorems.Thm_BandParity_sign_mul_modEq

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
namespace BandParity
theorem _root_.solution {ι : Type*} (X : Finset ι) (σ τ : ι → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ x ∈ X, τ x = 1 ∨ τ x = -1) :
    ∑ x ∈ X, σ x * τ x ≡ ∑ x ∈ X, σ x + ∑ x ∈ X, τ x - X.card [ZMOD 4] := by
  induction X using Finset.cons_induction with
  | empty => simp
  | cons a X ha ih =>
    rw [sum_cons, sum_cons, sum_cons, card_cons]
    have h1 := sign_mul_modEq (hσ a (mem_cons_self a X)) (hτ a (mem_cons_self a X))
    have h2 := ih (fun x hx => hσ x (mem_cons_of_mem hx)) (fun x hx => hτ x (mem_cons_of_mem hx))
    have := Int.ModEq.add h1 h2
    push_cast
    exact this.trans (by ring_nf; rfl)
end BandParity
