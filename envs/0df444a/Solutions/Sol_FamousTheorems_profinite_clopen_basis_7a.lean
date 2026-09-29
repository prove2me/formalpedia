-- Prove2me | solution 1 for FamousTheorems.profinite_clopen_basis_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:59:02.248203+00:00
-- url     : https://prove2.me/submissions/59372916-309b-4c91-a2ab-297cce95e814

import Mathlib

theorem solution (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X] :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  isTopologicalBasis_isClopen
