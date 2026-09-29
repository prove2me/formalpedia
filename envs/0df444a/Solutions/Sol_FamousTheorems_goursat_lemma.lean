-- Prove2me | solution 1 for FamousTheorems.goursat_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:29.959923+00:00
-- url     : https://prove2.me/submissions/cb1ac995-e822-46c2-a939-ab028f5e6be8

import Mathlib

theorem solution {G H : Type*} [Group G] [Group H] (I : Subgroup (G × H)) :
    ∃ (G' : Subgroup G) (H' : Subgroup H) (M : Subgroup G') (N : Subgroup H') (_ : M.Normal)
      (_ : N.Normal) (e : G' ⧸ M ≃* H' ⧸ N),
      I = (e.toMonoidHom.graph.comap ((QuotientGroup.mk' M).prodMap (QuotientGroup.mk' N))).map
        (G'.subtype.prodMap H'.subtype) :=
  Subgroup.goursat
