-- Prove2me | solution 1 for FamousTheorems.zariski_main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:58:53.307971+00:00
-- url     : https://prove2.me/submissions/827fecbf-22f7-45d1-80e2-754f426cbc20

import Mathlib

open AlgebraicGeometry

theorem solution {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : f.normalization.Opens, CategoryTheory.IsIso (f.toNormalization ∣_ U) ∧
      ((TopologicalSpace.Opens.map f.toNormalization.base).obj U).carrier = {x : X | f.QuasiFiniteAt x} :=
  f.exists_isIso_morphismRestrict_toNormalization
