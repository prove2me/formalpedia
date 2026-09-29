-- Prove2me | solution 1 for FamousTheorems.maschke_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:17:12.645382+00:00
-- url     : https://prove2.me/submissions/e25ebbef-cc21-4544-9ad4-556f709bfa49

import Mathlib

theorem solution {k : Type*} [Field k] {G : Type*} [Group G] [Finite G] [NeZero (Nat.card G : k)] {V : Type*}
    [AddCommGroup V] [Module (MonoidAlgebra k G) V] (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  MonoidAlgebra.Submodule.exists_isCompl p
