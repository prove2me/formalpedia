-- Prove2me | solution 1 for FamousTheorems.gordan_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:11:24.350512+00:00
-- url     : https://prove2.me/submissions/3705c54b-1693-49d3-99d1-b67adededaee

import Mathlib

theorem solution {M N : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M] [IsOrderedCancelMonoid M]
    [CanonicallyOrderedMul M] [Monoid N] [IsCancelMul N] (f g : M →* N) : (f.eqLocusM g).FG :=
  Submonoid.fg_eqLocusM f g
