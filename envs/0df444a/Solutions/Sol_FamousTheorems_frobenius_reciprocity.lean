-- Prove2me | solution 1 for FamousTheorems.frobenius_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:06:53.63056+00:00
-- url     : https://prove2.me/submissions/af2f5526-02f9-433d-b202-d97c969b5d5c

import Mathlib

universe u

theorem solution (k : Type u) {G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H) :
    Nonempty (CategoryTheory.Adjunction (Rep.indFunctor k φ : CategoryTheory.Functor (Rep.{u} k G) (Rep.{u} k H))
      (Rep.resFunctor φ : CategoryTheory.Functor (Rep.{u} k H) (Rep.{u} k G))) :=
  ⟨Rep.indResAdjunction k φ⟩
