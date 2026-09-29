-- Prove2me | solution 1 for FamousTheorems.qcqs_lemma_basic_open_localization_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:06:40.495334+00:00
-- url     : https://prove2.me/submissions/80850348-0c39-4857-a6cf-ce3d8ecc6895

import Mathlib

open Opposite

theorem solution {X : AlgebraicGeometry.Scheme} {U : X.Opens} (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    (f : X.presheaf.obj (op U)) : IsLocalization.Away f (X.presheaf.obj (op (X.basicOpen f))) :=
  AlgebraicGeometry.isLocalization_basicOpen_of_qcqs hU hU' f
