-- Prove2me | solution 1 for FamousTheorems.nobeling_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:24:38.734701+00:00
-- url     : https://prove2.me/submissions/a2a8d8b4-31ad-4587-97e5-8cdffd6142ec

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    Module.Free ℤ (LocallyConstant X ℤ) :=
  LocallyConstant.freeOfProfinite (Profinite.of X)
