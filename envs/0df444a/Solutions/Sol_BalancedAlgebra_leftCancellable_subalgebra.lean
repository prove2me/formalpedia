-- Prove2me | solution 1 for BalancedAlgebra.leftCancellable_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:45:24.128547+00:00
-- url     : https://prove2.me/submissions/bdacda51-44e3-4ace-bb22-06bd6606c7c7

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

/-- In an association the left cancellable elements are closed under the partial product. -/
theorem leftCancellable_subalgebra {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) :
    P.IsSubalgebra {b : A | P.LeftCancellable b} := by
  intro a b c ha hb hab x y d hx hy
  have h1 : P.lprod a b x = some d := by simp [lprod, hab, hx]
  have h2 := assoc_l2r (hP b) h1
  rw [rprod_eq_some] at h2
  obtain ⟨w, hbx, haw⟩ := h2
  have h3 : P.lprod a b y = some d := by simp [lprod, hab, hy]
  have h4 := assoc_l2r (hP b) h3
  rw [rprod_eq_some] at h4
  obtain ⟨w', hby, haw'⟩ := h4
  have hw : w = w' := ha w w' d haw haw'
  exact hb x y w hbx (by rw [hw]; exact hby)

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) :
    P.IsSubalgebra {b : A | P.LeftCancellable b} :=
  BAFix.leftCancellable_subalgebra P hP
