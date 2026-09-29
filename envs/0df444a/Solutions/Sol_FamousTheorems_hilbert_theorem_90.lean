-- Prove2me | solution 1 for FamousTheorems.hilbert_theorem_90
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:27.137468+00:00
-- url     : https://prove2.me/submissions/28085c28-e648-4872-9737-42a8d31ec135

import Mathlib

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (f : (L ≃ₐ[K] L) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) : groupCohomology.IsMulCoboundary₁ f :=
  groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
