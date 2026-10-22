-- Prove2me | solution 1 for FiniteMagmaE677.not_pair_critical_of_prod
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-22T05:52:10.395811+00:00
-- url     : https://prove2.me/submissions/d66c772f-03d7-4106-8b00-2a26675e6618

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# A product of two nontrivial magmas has no pair-critical point where `E255` fails

Let `op` be the componentwise operation of `op₁` on `α` and `op₂` on `β`, with `α` and `β`
each of at least two elements, and write `q z = ((z ◇ z) ◇ z) ◇ z`.  Suppose that every
congruence of `op` relating two distinct elements relates `z` and `q z`.  Then `q z = z`.

## Proof

* `q` is a term, so it is computed in each coordinate.
* The kernel of the first projection, `p.1 = p'.1`, is a congruence of `op`.  It relates the
  distinct elements `(z.1, b₁)` and `(z.1, b₂)` for `b₁ ≠ b₂` in `β`.  So it relates `z` and
  `q z`: `z.1 = (q z).1` (`fst_eq`).
* In the same way the kernel of the second projection gives `z.2 = (q z).2` (`snd_eq`).
* So `q z = z`.

Neither `E677` nor finiteness is used.  Ported from `lean/E677/CriticalCore.lean`
(`q_fst_eq_of_pairCritical_prod`, `q_snd_eq_of_pairCritical_prod`,
`not_pairCritical_prod_of_q_ne`) of a private repo (Adam McKenna).
-/

universe u v
open FiniteMagmaE677

namespace ProdHelpers

variable {α : Type*} {β : Type*} (op₁ : α → α → α) (op₂ : β → β → β)
  (op : α × β → α × β → α × β)

/-- The kernel of the first projection relates `z` and `q z`. -/
theorem fst_eq (hop : ∀ p r : α × β, op p r = (op₁ p.1 r.1, op₂ p.2 r.2)) (z : α × β)
    (hpc : ∀ r : α × β → α × β → Prop, Equivalence r →
      (∀ a a' b b' : α × β, r a a' → r b b' → r (op a b) (op a' b')) →
      ∀ a b : α × β, a ≠ b → r a b → r z (op (op (op z z) z) z))
    {b₁ b₂ : β} (hb : b₁ ≠ b₂) :
    z.1 = (op (op (op z z) z) z).1 :=
  hpc (fun p p' => p.1 = p'.1) ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
    (fun a a' b b' ha hb' => by rw [hop, hop]; exact congrArg₂ op₁ ha hb')
    (z.1, b₁) (z.1, b₂) (fun he => hb (congrArg Prod.snd he)) rfl

/-- The kernel of the second projection relates `z` and `q z`. -/
theorem snd_eq (hop : ∀ p r : α × β, op p r = (op₁ p.1 r.1, op₂ p.2 r.2)) (z : α × β)
    (hpc : ∀ r : α × β → α × β → Prop, Equivalence r →
      (∀ a a' b b' : α × β, r a a' → r b b' → r (op a b) (op a' b')) →
      ∀ a b : α × β, a ≠ b → r a b → r z (op (op (op z z) z) z))
    {a₁ a₂ : α} (ha : a₁ ≠ a₂) :
    z.2 = (op (op (op z z) z) z).2 :=
  hpc (fun p p' => p.2 = p'.2) ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
    (fun a a' b b' ha' hb => by rw [hop, hop]; exact congrArg₂ op₂ ha' hb)
    (a₁, z.2) (a₂, z.2) (fun he => ha (congrArg Prod.fst he)) rfl

end ProdHelpers

theorem solution
{α : Type u} {β : Type v} [Nontrivial α] [Nontrivial β]
(op₁ : α → α → α) (op₂ : β → β → β) (op : α × β → α × β → α × β)
(hop : ∀ p r : α × β, op p r = (op₁ p.1 r.1, op₂ p.2 r.2))
(z : α × β) (hz : op (op (op z z) z) z ≠ z) :
¬ ∀ r : α × β → α × β → Prop, Equivalence r →
  (∀ a a' b b' : α × β, r a a' → r b b' → r (op a b) (op a' b')) →
  ∀ a b : α × β, a ≠ b → r a b → r z (op (op (op z z) z) z) := by
  intro hpc
  obtain ⟨a₁, a₂, ha⟩ := exists_pair_ne α
  obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  exact hz (Prod.ext (ProdHelpers.fst_eq op₁ op₂ op hop z hpc hb).symm
    (ProdHelpers.snd_eq op₁ op₂ op hop z hpc ha).symm)

#print axioms solution
