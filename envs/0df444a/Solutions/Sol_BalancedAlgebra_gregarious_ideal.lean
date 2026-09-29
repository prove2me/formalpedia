-- Prove2me | solution 1 for BalancedAlgebra.gregarious_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:53:16.111994+00:00
-- url     : https://prove2.me/submissions/e1e92b7b-14c8-4014-ac15-df5b775f5219

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

/-- Closure of the society on the right (Winkler §4.2). -/
theorem society_mul_right {P : PartialAlgebra A} {b c e : A}
    (hbg : P.Gregarious b) (hb : P.Associating b) (hc : P.Associating c)
    (hbc : P.op b c = some e) : P.Gregarious e := by
  rintro p q ⟨r, hpe⟩ ⟨m, heq⟩
  have h1 : P.rprod p b c = some r := by simp [rprod, hbc, hpe]
  have h2 := assoc_r2l hb h1
  rw [lprod_eq_some] at h2
  obtain ⟨s, hpb, hsc⟩ := h2
  have h3 : P.lprod b c q = some m := by simp [lprod, hbc, heq]
  have h4 := assoc_l2r hc h3
  rw [rprod_eq_some] at h4
  obtain ⟨w, hcq, hbw⟩ := h4
  rcases hbg p w ⟨s, hpb⟩ ⟨m, hbw⟩ with hL | hR
  · left
    rw [show P.lprod p b w = P.op s w from by simp [lprod, hpb]] at hL
    obtain ⟨t, hsw⟩ := hL
    have h5 : P.rprod s c q = some t := by simp [rprod, hcq, hsw]
    have h6 := assoc_r2l hc h5
    have hrq : P.op r q = some t := by simpa [lprod, hsc] using h6
    exact ⟨t, by rw [lprod_eq_some]; exact ⟨r, hpe, hrq⟩⟩
  · right
    rw [show P.rprod p b w = P.op p m from by simp [rprod, hbw]] at hR
    obtain ⟨t, hpm⟩ := hR
    exact ⟨t, by rw [rprod_eq_some]; exact ⟨m, heq, hpm⟩⟩

/-- Closure of the society on the left (Winkler §4.2). -/
theorem society_mul_left {P : PartialAlgebra A} {a b e : A}
    (ha : P.Associating a) (hbg : P.Gregarious b) (hb : P.Associating b)
    (hab : P.op a b = some e) : P.Gregarious e := by
  rintro p q ⟨r, hpe⟩ ⟨m, heq⟩
  have h1 : P.rprod p a b = some r := by simp [rprod, hab, hpe]
  have h2 := assoc_r2l ha h1
  rw [lprod_eq_some] at h2
  obtain ⟨s, hpa, hsb⟩ := h2
  have h3 : P.lprod a b q = some m := by simp [lprod, hab, heq]
  have h4 := assoc_l2r hb h3
  rw [rprod_eq_some] at h4
  obtain ⟨w, hbq, haw⟩ := h4
  rcases hbg s q ⟨r, hsb⟩ ⟨w, hbq⟩ with hL | hR
  · left
    rw [show P.lprod s b q = P.op r q from by simp [lprod, hsb]] at hL
    obtain ⟨t, hrq⟩ := hL
    exact ⟨t, by rw [lprod_eq_some]; exact ⟨r, hpe, hrq⟩⟩
  · right
    rw [show P.rprod s b q = P.op s w from by simp [rprod, hbq]] at hR
    obtain ⟨t, hsw⟩ := hR
    have h5 : P.lprod p a w = some t := by rw [lprod_eq_some]; exact ⟨s, hpa, hsw⟩
    have h6 := assoc_l2r ha h5
    have hpm : P.op p m = some t := by simpa [rprod, haw] using h6
    exact ⟨t, by rw [rprod_eq_some]; exact ⟨m, heq, hpm⟩⟩

/-- **The gregarious ideal.**  In an association every element is associating, so the two
society closure computations say exactly that the gregarious elements absorb multiplication
on both sides. -/
theorem gregarious_ideal {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) :
    P.LeftIdeal {b : A | P.Gregarious b} ∧ P.RightIdeal {b : A | P.Gregarious b} := by
  constructor
  · intro a b c hb hab
    exact society_mul_left (hP a) hb (hP b) hab
  · intro a b c ha hab
    exact society_mul_right ha (hP a) (hP b) hab

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) :
    P.LeftIdeal {b : A | P.Gregarious b} ∧ P.RightIdeal {b : A | P.Gregarious b} :=
  BAFix.gregarious_ideal P hP
