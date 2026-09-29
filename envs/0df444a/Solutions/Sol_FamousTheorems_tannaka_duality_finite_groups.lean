-- Prove2me | solution 1 for FamousTheorems.tannaka_duality_finite_groups
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:09:20.434703+00:00
-- url     : https://prove2.me/submissions/a570964e-965f-4cdb-801f-0cdefacc63e1

import Mathlib

universe u

theorem solution (k G : Type u) [CommRing k] [IsDomain k] [Group G] [Finite G] :
    Function.Bijective (TannakaDuality.FiniteGroup.equivHom k G) :=
  ⟨TannakaDuality.FiniteGroup.equivHom_injective, TannakaDuality.FiniteGroup.equivHom_surjective⟩
