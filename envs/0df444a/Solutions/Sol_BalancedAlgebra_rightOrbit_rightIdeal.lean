-- Prove2me | solution 1 for BalancedAlgebra.rightOrbit_rightIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:45:17.595269+00:00
-- url     : https://prove2.me/submissions/e5827c19-43d6-48fb-8bb0-c9dce06a0577

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

/-- In an association, right orbits are principal right ideals. -/
theorem rightOrbit_rightIdeal {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) (a : A) :
    P.RightIdeal (P.rightOrbit a) := by
  intro x y z hx hop
  obtain ⟨b, hb⟩ := hx
  have h1 : P.lprod a b y = some z := by rw [lprod_eq_some]; exact ⟨x, hb, hop⟩
  have h2 := assoc_l2r (hP b) h1
  rw [rprod_eq_some] at h2
  obtain ⟨w, _, haw⟩ := h2
  exact ⟨w, haw⟩

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) (a : A) :
    P.RightIdeal (P.rightOrbit a) :=
  BAFix.rightOrbit_rightIdeal P hP a
