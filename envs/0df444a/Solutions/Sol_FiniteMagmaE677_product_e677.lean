-- Prove2me | solution 1 for FiniteMagmaE677.product_e677
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:20:11.270389+00:00
-- url     : https://prove2.me/submissions/39e6d02a-849e-4038-83ee-25bd1dfb5ec5

import Definitions.Def_FiniteMagmaE677

/-!
# Products of E677 magmas

Equational classes are closed under products. Concretely: if `op₁` on `α`
and `op₂` on `β` both satisfy E677, then the componentwise operation on
`α × β` satisfies E677, and it satisfies E255 as soon as both factors do.
-/

universe u v

theorem FiniteMagmaE677.product_e677 {α : Type u} {β : Type v}
    (op₁ : α → α → α) (op₂ : β → β → β)
    (h₁ : FiniteMagmaE677.E677 op₁) (h₂ : FiniteMagmaE677.E677 op₂) :
    FiniteMagmaE677.E677 (fun p q : α × β => (op₁ p.1 q.1, op₂ p.2 q.2)) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  exact Prod.ext (h₁ x₁ y₁) (h₂ x₂ y₂)

theorem FiniteMagmaE677.product_e255 {α : Type u} {β : Type v}
    (op₁ : α → α → α) (op₂ : β → β → β)
    (h₁ : FiniteMagmaE677.E255 op₁) (h₂ : FiniteMagmaE677.E255 op₂) :
    FiniteMagmaE677.E255 (fun p q : α × β => (op₁ p.1 q.1, op₂ p.2 q.2)) := by
  rintro ⟨x₁, x₂⟩
  exact Prod.ext (h₁ x₁) (h₂ x₂)

theorem solution {α : Type u} {β : Type v}
    (op₁ : α → α → α) (op₂ : β → β → β)
    (h₁ : FiniteMagmaE677.E677 op₁) (h₂ : FiniteMagmaE677.E677 op₂) :
    FiniteMagmaE677.E677 (fun p q : α × β => (op₁ p.1 q.1, op₂ p.2 q.2)) :=
  FiniteMagmaE677.product_e677 op₁ op₂ h₁ h₂

