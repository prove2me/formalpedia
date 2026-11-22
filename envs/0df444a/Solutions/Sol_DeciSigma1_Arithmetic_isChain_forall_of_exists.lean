-- Prove2me | solution 1 for DeciSigma1.Arithmetic.isChain_forall_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:18.617798+00:00
-- url     : https://prove2.me/submissions/e4cb5b39-e883-4bc6-9799-f254ab5a4270

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
namespace DeciSigma1.Arithmetic
theorem _root_.solution {R : β → β → Prop} {Q : β → Prop} :
    ∀ {p : List β}, p.IsChain R → (∀ x ∈ p, ∀ y ∈ p, R x y → (Q x ↔ Q y)) →
      (∃ x ∈ p, Q x) → ∀ x ∈ p, Q x
  | [], _, _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | [a], _, _, ⟨x, hx, hq⟩ => by
    intro y hy
    rw [List.mem_singleton] at hx hy
    subst hx; subst hy; exact hq
  | a :: b :: l, hc, hR, ⟨x, hx, hq⟩ => by
    rw [List.isChain_cons_cons] at hc
    have hR' : ∀ x ∈ b :: l, ∀ y ∈ b :: l, R x y → (Q x ↔ Q y) :=
      fun x hx y hy => hR x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    have hex : ∃ x ∈ b :: l, Q x := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, List.mem_cons_self, (hR x List.mem_cons_self b
          (List.mem_cons_of_mem _ List.mem_cons_self) hc.1).mp hq⟩
      · exact ⟨x, hx, hq⟩
    have ih := solution hc.2 hR' hex
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (hR y List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self) hc.1).mpr
        (ih b List.mem_cons_self)
    · exact ih y hy
end DeciSigma1.Arithmetic
