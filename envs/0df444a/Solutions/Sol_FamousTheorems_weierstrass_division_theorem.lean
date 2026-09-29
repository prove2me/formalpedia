-- Prove2me | solution 1 for FamousTheorems.weierstrass_division_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:48:37.928589+00:00
-- url     : https://prove2.me/submissions/ecdbf92b-87d6-43b1-b5f0-f39e91ec9499

import Mathlib

theorem solution {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (f : PowerSeries A)
    {g : PowerSeries A} (hg : PowerSeries.map (IsLocalRing.residue A) g ≠ 0) :
    ∃ (q : PowerSeries A) (r : Polynomial A), f.IsWeierstrassDivision g q r :=
  PowerSeries.exists_isWeierstrassDivision f hg
