-- Prove2me | solution 1 for CompactnessConjecture.symplecticPoint_sup_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/5a95c475-e1b8-4220-a607-be0231e27651

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {p q : SymplecticPoint K} (hpq : p ≠ q) :
    Module.finrank K
      (p.1 ⊔ q.1 : Submodule K (SymplecticVector K)) = 2 := by
  have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
  have hd : Disjoint p.1 q.1 :=
    (Submodule.isAtom_iff_finrank_eq_one.mpr p.2).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.mpr q.2) hne
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
  rw [hd.eq_bot, finrank_bot, p.2, q.2] at hrank
  omega
end CompactnessConjecture
