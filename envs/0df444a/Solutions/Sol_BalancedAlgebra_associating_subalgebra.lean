-- Prove2me | solution 1 for BalancedAlgebra.associating_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:45:14.878283+00:00
-- url     : https://prove2.me/submissions/fc64d134-61a4-4590-bd9e-37b9b118a3d5

import Mathlib
import Definitions.Def_BalancedAlgebra_core

set_option linter.unusedSectionVars false

namespace BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra

variable {A : Type*}

/-- An associating middle factor transports a left-bracketed value to the right bracketing. -/
theorem assoc_l2r {P : PartialAlgebra A} {b : A} (hb : P.Associating b) {a c t : A}
    (h : P.lprod a b c = some t) : P.rprod a b c = some t := by
  obtain ⟨t', ht'⟩ := (hb a c).1.1 ⟨t, h⟩
  have e : t = t' := (hb a c).2 t t' h ht'
  rw [e]; exact ht'

/-- An associating middle factor transports a right-bracketed value to the left bracketing. -/
theorem assoc_r2l {P : PartialAlgebra A} {b : A} (hb : P.Associating b) {a c t : A}
    (h : P.rprod a b c = some t) : P.lprod a b c = some t := by
  obtain ⟨t', ht'⟩ := (hb a c).1.2 ⟨t, h⟩
  have e : t = t' := ((hb a c).2 t' t ht' h).symm
  rw [e]; exact ht'

/-- **The bracket chase.**  If `a` and `b` are associating and `a · b = c`, then `c` is
associating.  Both directions are the same five-step walk, run in opposite order:
`(p·c)·q → (p·a)·b → (s·b)·q → s·(b·q) → (p·a)·w → p·(a·w) → p·(c·q)`. -/
theorem mul_associating {P : PartialAlgebra A} {a b c : A}
    (ha : P.Associating a) (hb : P.Associating b) (hab : P.op a b = some c) :
    P.Associating c := by
  have key : ∀ p q t : A, P.lprod p c q = some t → P.rprod p c q = some t := by
    intro p q t h
    rw [lprod_eq_some] at h
    obtain ⟨r, hpc, hrq⟩ := h
    have h1 : P.rprod p a b = some r := by simp [rprod, hab, hpc]
    have h2 := assoc_r2l ha h1
    rw [lprod_eq_some] at h2
    obtain ⟨s, hps, hsb⟩ := h2
    have h3 : P.lprod s b q = some t := by rw [lprod_eq_some]; exact ⟨r, hsb, hrq⟩
    have h4 := assoc_l2r hb h3
    rw [rprod_eq_some] at h4
    obtain ⟨w, hbq, hsw⟩ := h4
    have h5 : P.lprod p a w = some t := by rw [lprod_eq_some]; exact ⟨s, hps, hsw⟩
    have h6 := assoc_l2r ha h5
    rw [rprod_eq_some] at h6
    obtain ⟨v, haw, hpv⟩ := h6
    have h7 : P.rprod a b q = some v := by simp [rprod, hbq, haw]
    have h8 := assoc_r2l hb h7
    have hcq : P.op c q = some v := by simpa [lprod, hab] using h8
    rw [rprod_eq_some]; exact ⟨v, hcq, hpv⟩
  have key' : ∀ p q t : A, P.rprod p c q = some t → P.lprod p c q = some t := by
    intro p q t h
    rw [rprod_eq_some] at h
    obtain ⟨v, hcq, hpv⟩ := h
    have h1 : P.lprod a b q = some v := by simp [lprod, hab, hcq]
    have h2 := assoc_l2r hb h1
    rw [rprod_eq_some] at h2
    obtain ⟨w, hbq, haw⟩ := h2
    have h3 : P.rprod p a w = some t := by simp [rprod, haw, hpv]
    have h4 := assoc_r2l ha h3
    rw [lprod_eq_some] at h4
    obtain ⟨s, hps, hsw⟩ := h4
    have h5 : P.rprod s b q = some t := by simp [rprod, hbq, hsw]
    have h6 := assoc_r2l hb h5
    rw [lprod_eq_some] at h6
    obtain ⟨r, hsb, hrq⟩ := h6
    have h7 : P.lprod p a b = some r := by rw [lprod_eq_some]; exact ⟨s, hps, hsb⟩
    have h8 := assoc_l2r ha h7
    have hpc : P.op p c = some r := by simpa [rprod, hab] using h8
    rw [lprod_eq_some]; exact ⟨r, hpc, hrq⟩
  intro p q
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨t, ht⟩; exact ⟨t, key p q t ht⟩
  · rintro ⟨t, ht⟩; exact ⟨t, key' p q t ht⟩
  · intro x y hx hy
    have hxx := key p q x hx
    rw [hxx] at hy
    exact Option.some.inj hy

/-- The associating elements form a subalgebra. -/
theorem associating_subalgebra {A : Type*} (P : PartialAlgebra A) :
    P.IsSubalgebra {b : A | P.Associating b} := by
  intro a b c ha hb hab
  exact mul_associating ha hb hab

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) :
    P.IsSubalgebra {b : A | P.Associating b} :=
  BAFix.associating_subalgebra P
