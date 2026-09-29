-- Prove2me | solution 1 for FamousTheorems.normal_basis_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:52:44.006639+00:00
-- url     : https://prove2.me/submissions/1b84e9fb-b8d8-4293-a7a1-b191d3557028

import Mathlib

theorem solution (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L => σ x :=
  exists_linearIndependent_algEquiv_apply K L
