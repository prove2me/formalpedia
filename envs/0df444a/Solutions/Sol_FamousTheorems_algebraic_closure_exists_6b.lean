-- Prove2me | solution 1 for FamousTheorems.algebraic_closure_exists_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:14:10.541972+00:00
-- url     : https://prove2.me/submissions/d3dbbdb7-f454-4698-b925-831498c84d8c

import Mathlib

theorem solution (k : Type*) [Field k] : IsAlgClosure k (AlgebraicClosure k) :=
  inferInstance
