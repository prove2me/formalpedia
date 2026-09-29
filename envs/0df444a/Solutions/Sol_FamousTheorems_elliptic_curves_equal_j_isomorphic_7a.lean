-- Prove2me | solution 1 for FamousTheorems.elliptic_curves_equal_j_isomorphic_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:07:44.993174+00:00
-- url     : https://prove2.me/submissions/44285874-cc1b-4b37-80cd-b842dfc785ec

import Mathlib

theorem solution {F : Type*} [Field F] [IsSepClosed F] (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (h : E.j = E'.j) : ∃ C : WeierstrassCurve.VariableChange F, C • E = E' :=
  E.exists_variableChange_of_j_eq E' h
