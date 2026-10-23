-- Prove2me | solution 1 for FiniteMagmaE677.e255_of_twisted_extension_of_right_divisible
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-23T01:10:23.009586+00:00
-- url     : https://prove2.me/submissions/22735ce0-50bb-445c-b7b4-ad67cde7bf54

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# Twisted extensions over a right-divisible fibre satisfy `E255`

`op` is an operation on `Q × E` that satisfies `E677`.  Off the blocks `(e, e)` with
`opQ e e = e` it has the form `(x, s) ◇ (y, t) = (x ◇ y, φ x y s ◇ ψ x y t)` with automorphisms
`φ x y`, `ψ x y` of `(E, opE)`.  `opQ` satisfies `E255`, `E255` holds at the points over each
idempotent, and `E` satisfies the condition (R) of `hR`.

## Proof

* Points over an idempotent `x`: hypothesis `hidem`.
* Let `opQ x x ≠ x`, `v = (x ◇ x) ◇ x` and `x' = x ◇ v`.  The blocks `(x, w)` for every `w` and
  the block `(v, x)` are twisted, and `v ◇ x = x` (`E255` for `opQ`).  The first coordinate of
  `E677` for `op` at `(x, s)`, `(x, s)` gives `x ◇ (x ◇ v) = x`.
* The second coordinate of `E677` for `op` at `(x, s')`, `(v, (φ v x)⁻¹ t)` uses the blocks
  `(v, x)`, `(x, v)`, `(x, x')`.  It is the identity of (R) for the automorphisms
  `α = ψ v x * φ x x'`, `a = D * φ x v`, `b = D * φ x v * ψ v x`,
  `c = D * ψ x v * (φ v x)⁻¹`, where `D = ψ v x * ψ x x'`.
* (R) gives `r` with `r ◇ b s = a s`.  Then `f = (v, (φ v x)⁻¹ ((D * φ x v)⁻¹ r))` satisfies
  `f ◇ (x, s) = (x, s)`.
* In a finite `E677` magma, a point with such an `f` satisfies `E255` (ETP blueprint, Lemma 13.2):
  `f` and `(p ◇ p) ◇ p` both solve `p ◇ (p ◇ u) = p`, and left multiplications are injective.

Ported from `lean/E677/TwistedExtension.lean`
(`Eq677.autTwistedOffIdempotents_implies_eq255_of_rightDivisible`) of a private repo
(Adam McKenna); the `Magma` instances there are the explicit operations here.
-/

universe u v
open FiniteMagmaE677

namespace TwistedHelpers

/-- A product of two automorphisms of `(E, opE)` is an automorphism. -/
theorem aut_mul {E : Type*} {opE : E → E → E} {f g : Equiv.Perm E}
    (hf : ∀ a b : E, f (opE a b) = opE (f a) (f b))
    (hg : ∀ a b : E, g (opE a b) = opE (g a) (g b)) :
    ∀ a b : E, (f * g) (opE a b) = opE ((f * g) a) ((f * g) b) := by
  intro a b
  simp only [Equiv.Perm.mul_apply, hg a b]
  exact hf _ _

/-- The inverse of an automorphism of `(E, opE)` is an automorphism. -/
theorem aut_inv {E : Type*} {opE : E → E → E} {f : Equiv.Perm E}
    (hf : ∀ a b : E, f (opE a b) = opE (f a) (f b)) :
    ∀ a b : E, f⁻¹ (opE a b) = opE (f⁻¹ a) (f⁻¹ b) := by
  intro a b
  apply f.injective
  rw [hf, Equiv.Perm.inv_def, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

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

end TwistedHelpers

theorem solution
{Q : Type u} {E : Type v} [Finite Q] [Finite E]
(opQ : Q → Q → Q) (opE : E → E → E) (op : Q × E → Q × E → Q × E)
(φ ψ : Q → Q → Equiv.Perm E)
(hQ : FiniteMagmaE677.E255 opQ) (h : FiniteMagmaE677.E677 op)
(htw : ∀ (x y : Q) (s t : E), ¬ (x = y ∧ opQ x x = x) →
  op (x, s) (y, t) = (opQ x y, opE (φ x y s) (ψ x y t)))
(hidem : ∀ x : Q, opQ x x = x → ∀ s : E,
  (x, s) = op (op (op (x, s) (x, s)) (x, s)) (x, s))
(hφ : ∀ (x y : Q) (a b : E), φ x y (opE a b) = opE (φ x y a) (φ x y b))
(hψ : ∀ (x y : Q) (a b : E), ψ x y (opE a b) = opE (ψ x y a) (ψ x y b))
(hR : ∀ α a b c : Equiv.Perm E,
  (∀ u w : E, α (opE u w) = opE (α u) (α w)) →
  (∀ u w : E, a (opE u w) = opE (a u) (a w)) →
  (∀ u w : E, b (opE u w) = opE (b u) (b w)) →
  (∀ u w : E, c (opE u w) = opE (c u) (c w)) →
  (∀ s t : E, s = opE t (opE (α s) (opE (opE (a t) (b s)) (c t)))) →
  ∀ s : E, ∃ r : E, opE r (b s) = a s) :
FiniteMagmaE677.E255 op := by
  rintro ⟨x, s⟩
  by_cases hx : opQ x x = x
  · exact hidem x hx s
  · have happ : ∀ (f : Equiv.Perm E) (y : E), f (f⁻¹ y) = y := fun f y => f.apply_symm_apply y
    -- every block in the row of `x` is twisted
    have hxw : ∀ (w : Q) (a b : E), op (x, a) (w, b) = (opQ x w, opE (φ x w a) (ψ x w b)) :=
      fun w a b => htw x w a b fun h => hx h.2
    obtain ⟨v, hvblk, hxxv⟩ : ∃ v : Q,
        (∀ a b : E, op (v, a) (x, b) = (x, opE (φ v x a) (ψ v x b))) ∧ opQ x (opQ x v) = x := by
      have hvx : opQ (opQ (opQ x x) x) x = x := (hQ x).symm
      refine ⟨opQ (opQ x x) x, fun a b => ?_, ?_⟩
      · rw [htw _ x a b ?_, hvx]
        rintro ⟨h1, h2⟩
        rw [h1] at h2
        exact hx h2
      · have hxx : ∀ a b : E, op (opQ x x, a) (x, b) =
            (opQ (opQ x x) x, opE (φ (opQ x x) x a) (ψ (opQ x x) x b)) :=
          fun a b => htw _ x a b fun h => hx h.1
        have h' := congrArg Prod.fst (h (x, s) (x, s))
        simp only [hxw, hxx] at h'
        exact h'.symm
    -- the second coordinate of `E677` at `(x, s')`, `(v, (φ v x)⁻¹ t)`
    have hsol : ∀ s' t : E, s' = opE t (opE ((ψ v x * φ x (opQ x v)) s')
        (opE (opE ((ψ v x * ψ x (opQ x v) * φ x v) t)
          ((ψ v x * ψ x (opQ x v) * φ x v * ψ v x) s'))
          ((ψ v x * ψ x (opQ x v) * ψ x v * (φ v x)⁻¹) t))) := by
      intro s' t
      have h' := congrArg Prod.snd (h (x, s') (v, (φ v x)⁻¹ t))
      simp only [hvblk, hxw, hxxv, hφ, hψ, happ] at h'
      simp only [Equiv.Perm.mul_apply]
      exact h'
    have ha : ∀ u w : E, (ψ v x * ψ x (opQ x v) * φ x v) (opE u w) =
        opE ((ψ v x * ψ x (opQ x v) * φ x v) u) ((ψ v x * ψ x (opQ x v) * φ x v) w) :=
      TwistedHelpers.aut_mul (TwistedHelpers.aut_mul (hψ _ _) (hψ _ _)) (hφ _ _)
    obtain ⟨r, hr⟩ := hR (ψ v x * φ x (opQ x v)) (ψ v x * ψ x (opQ x v) * φ x v)
      (ψ v x * ψ x (opQ x v) * φ x v * ψ v x) (ψ v x * ψ x (opQ x v) * ψ x v * (φ v x)⁻¹)
      (TwistedHelpers.aut_mul (hψ _ _) (hφ _ _)) ha (TwistedHelpers.aut_mul ha (hψ _ _))
      (TwistedHelpers.aut_mul
        (TwistedHelpers.aut_mul (TwistedHelpers.aut_mul (hψ _ _) (hψ _ _)) (hψ _ _))
        (TwistedHelpers.aut_inv (hφ _ _)))
      hsol s
    simp only [Equiv.Perm.mul_apply] at hr
    -- pull `r` back through `ψ v x * ψ x (x ◇ v) * φ x v`
    have hr' : opE ((φ x v)⁻¹ ((ψ x (opQ x v))⁻¹ ((ψ v x)⁻¹ r))) (ψ v x s) = s := by
      apply (φ x v).injective
      apply (ψ x (opQ x v)).injective
      apply (ψ v x).injective
      simp only [hφ, hψ, happ]
      exact hr
    apply TwistedHelpers.eq255_at_of_fixer op h
      (f := (v, (φ v x)⁻¹ ((φ x v)⁻¹ ((ψ x (opQ x v))⁻¹ ((ψ v x)⁻¹ r)))))
    rw [hvblk, happ, hr']

#print axioms solution
