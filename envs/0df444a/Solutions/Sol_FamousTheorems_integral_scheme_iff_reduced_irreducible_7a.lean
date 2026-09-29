-- Prove2me | solution 1 for FamousTheorems.integral_scheme_iff_reduced_irreducible_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:07:34.761441+00:00
-- url     : https://prove2.me/submissions/21636f55-e722-4383-bad5-c96a1686e162

import Mathlib

theorem solution (X : AlgebraicGeometry.Scheme) :
    AlgebraicGeometry.IsIntegral X ↔ IrreducibleSpace X ∧ AlgebraicGeometry.IsReduced X :=
  AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced X
