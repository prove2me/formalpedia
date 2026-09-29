-- Prove2me | solution 1 for FamousTheorems.shapiro_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:06:53.314758+00:00
-- url     : https://prove2.me/submissions/9a8240e3-0cb7-4bfa-a3c4-0c1f50f6094a

import Mathlib

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep.{u} k S) (n : ℕ) :
    Nonempty (CategoryTheory.Iso (groupCohomology (Rep.coind S.subtype A) n) (groupCohomology A n)) :=
  ⟨groupCohomology.coindIso A n⟩
