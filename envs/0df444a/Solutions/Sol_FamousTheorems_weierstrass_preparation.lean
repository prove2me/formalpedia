-- Prove2me | solution 1 for FamousTheorems.weierstrass_preparation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:20:31.268413+00:00
-- url     : https://prove2.me/submissions/c033f8ec-62b9-4e71-94ca-b50ebb2215ce

import Mathlib

theorem solution {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {g : PowerSeries A}
    (hg : PowerSeries.map (IsLocalRing.residue A) g ≠ 0) :
    ∃ (f : Polynomial A) (h : PowerSeries A), g.IsWeierstrassFactorization f h :=
  PowerSeries.exists_isWeierstrassFactorization hg
