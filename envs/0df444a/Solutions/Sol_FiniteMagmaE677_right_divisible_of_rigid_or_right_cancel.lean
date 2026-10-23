-- Prove2me | solution 1 for FiniteMagmaE677.right_divisible_of_rigid_or_right_cancel
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-23T01:11:55.491046+00:00
-- url     : https://prove2.me/submissions/6d5ae83e-5548-4171-94fe-bcf825f8a5fe

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# Condition (R) for a rigid fibre with `E255` and for a finite right-cancellative fibre

(R) for `(E, opE)`: for every quadruple `(α, a, b, c)` of automorphisms with
`s = t ◇ (α s ◇ ((a t ◇ b s) ◇ c t))` for all `s, t`, and every `s`, some `r` has
`r ◇ b s = a s`.

## Proof

* Rigid with `E255`: rigidity gives `a = b = 1`, and `r = (s ◇ s) ◇ s` has `r ◇ s = s` by `E255`.
* Finite and right-cancellative: the right multiplication by `b s` is injective on the finite
  `E`, so it is onto, and some `r` has `r ◇ b s = a s`.

Ported from `lean/E677/TwistedExtension.lean` (`Eq677.IsRightDivisible677.of_rigid`,
`Eq677.IsRightDivisible677.of_rightCancel`) of a private repo (Adam McKenna).
-/

universe u
open FiniteMagmaE677

theorem solution
{E : Type u} (opE : E → E → E)
(hE : ((∀ α a b c : Equiv.Perm E,
    (∀ u w : E, α (opE u w) = opE (α u) (α w)) →
    (∀ u w : E, a (opE u w) = opE (a u) (a w)) →
    (∀ u w : E, b (opE u w) = opE (b u) (b w)) →
    (∀ u w : E, c (opE u w) = opE (c u) (c w)) →
    (∀ s t : E, s = opE t (opE (α s) (opE (opE (a t) (b s)) (c t)))) →
    α = 1 ∧ a = 1 ∧ b = 1 ∧ c = 1) ∧ FiniteMagmaE677.E255 opE) ∨
  (Finite E ∧ ∀ b : E, Function.Injective (fun a : E => opE a b))) :
∀ α a b c : Equiv.Perm E,
  (∀ u w : E, α (opE u w) = opE (α u) (α w)) →
  (∀ u w : E, a (opE u w) = opE (a u) (a w)) →
  (∀ u w : E, b (opE u w) = opE (b u) (b w)) →
  (∀ u w : E, c (opE u w) = opE (c u) (c w)) →
  (∀ s t : E, s = opE t (opE (α s) (opE (opE (a t) (b s)) (c t)))) →
  ∀ s : E, ∃ r : E, opE r (b s) = a s := by
  intro α a b c hα ha hb hc hsol s
  rcases hE with ⟨hrig, hE255⟩ | ⟨hfin, hrc⟩
  · obtain ⟨-, rfl, rfl, -⟩ := hrig α a b c hα ha hb hc hsol
    exact ⟨opE (opE s s) s, (hE255 s).symm⟩
  · exact Finite.injective_iff_surjective.mp (hrc (b s)) (a s)

#print axioms solution
