-- Prove2me | solution 1 for FiniteMagmaE677.e255_of_twisted_extension_of_right_cancel
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-23T01:13:18.101778+00:00
-- url     : https://prove2.me/submissions/dd6fa43e-8380-45cf-aca0-e72e24d3d8ff

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# Permutation-twisted extensions over a finite right-cancellative fibre satisfy `E255`

`op` is an operation on `Q × E` that satisfies `E677`.  Off the blocks `(e, e)` with
`opQ e e = e` it has the form `(x, s) ◇ (y, t) = (x ◇ y, φ x y s ◇ ψ x y t)` with permutations
`φ x y`, `ψ x y` of `E`.  `Q` and `E` are finite, `opQ` satisfies `E255`, `E255` holds at the
points over each idempotent, and right multiplications of `(E, opE)` are injective.

## Proof

* Points over an idempotent `x`: hypothesis `hidem`.
* Let `opQ x x ≠ x` and `v = (x ◇ x) ◇ x`.  Then `v ◇ x = x` (`E255` for `opQ`), and the block
  `(v, x)` is not an idempotent diagonal block, so it is twisted.
* `a ↦ φ v x a ◇ ψ v x s` is injective (right cancellation, `φ v x` a permutation), so it is
  onto the finite `E`: some `a` gives `(v, a) ◇ (x, s) = (x, s)`.
* In a finite `E677` magma, a point with such an element satisfies `E255` (ETP blueprint,
  Lemma 13.2): the element and `(p ◇ p) ◇ p` both solve `p ◇ (p ◇ u) = p`, and left
  multiplications are injective.

No automorphism property of the twists and no equation on `E` is used.  Ported from
`lean/E677/TwistedExtension.lean` (`Eq677.autTwistedOffIdempotents_implies_eq255_of_rightCancel`)
of a private repo (Adam McKenna); the `Magma` instances there are the explicit operations here.
-/

universe u v
open FiniteMagmaE677

namespace TwistedRCHelpers

/-- In a finite magma that satisfies `E677`, a point `p` with an element `f` such that
`f ◇ p = p` satisfies `E255` (ETP blueprint, Lemma 13.2). -/
theorem eq255_at_of_fixer {M : Type*} [Finite M] (op : M → M → M)
    (hM : FiniteMagmaE677.E677 op) {p f : M} (hf : op f p = p) :
    p = op (op (op p p) p) p := by
  have hinj : ∀ y : M, Function.Injective (fun u => op y u) := fun y =>
    Finite.injective_iff_surjective.mpr fun x => ⟨op x (op (op y x) y), (hM x y).symm⟩
  have h1 : op p (op p f) = p := by
    have e := hM p f
    rw [hf] at e
    apply hinj f
    change op f (op p (op p f)) = op f p
    rw [hf]
    exact e.symm
  have h2 : op p (op p (op (op p p) p)) = p := (hM p p).symm
  have hfΦ : f = op (op p p) p := hinj p (hinj p (h1.trans h2.symm))
  rw [← hfΦ]
  exact hf.symm

end TwistedRCHelpers

theorem solution
{Q : Type u} {E : Type v} [Finite Q] [Finite E]
(opQ : Q → Q → Q) (opE : E → E → E) (op : Q × E → Q × E → Q × E)
(φ ψ : Q → Q → Equiv.Perm E)
(hQ : FiniteMagmaE677.E255 opQ) (h : FiniteMagmaE677.E677 op)
(htw : ∀ (x y : Q) (s t : E), ¬ (x = y ∧ opQ x x = x) →
  op (x, s) (y, t) = (opQ x y, opE (φ x y s) (ψ x y t)))
(hidem : ∀ x : Q, opQ x x = x → ∀ s : E,
  (x, s) = op (op (op (x, s) (x, s)) (x, s)) (x, s))
(hrc : ∀ b : E, Function.Injective (fun a : E => opE a b)) :
FiniteMagmaE677.E255 op := by
  rintro ⟨x, s⟩
  by_cases hx : opQ x x = x
  · exact hidem x hx s
  · have hvx : opQ (opQ (opQ x x) x) x = x := (hQ x).symm
    have hblock : ¬(opQ (opQ x x) x = x ∧
        opQ (opQ (opQ x x) x) (opQ (opQ x x) x) = opQ (opQ x x) x) := by
      rintro ⟨h1, h2⟩
      rw [h1] at h2
      exact hx h2
    have hsurj : Function.Surjective
        (fun a : E => opE (φ (opQ (opQ x x) x) x a) (ψ (opQ (opQ x x) x) x s)) :=
      Finite.injective_iff_surjective.mp fun a b hab =>
        (φ (opQ (opQ x x) x) x).injective (hrc (ψ (opQ (opQ x x) x) x s) hab)
    obtain ⟨a, ha⟩ := hsurj s
    apply TwistedRCHelpers.eq255_at_of_fixer op h (f := (opQ (opQ x x) x, a))
    rw [htw _ x a s hblock, hvx]
    exact Prod.ext rfl ha

#print axioms solution
