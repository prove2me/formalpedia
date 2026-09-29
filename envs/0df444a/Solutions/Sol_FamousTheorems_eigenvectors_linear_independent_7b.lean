-- Prove2me | solution 1 for FamousTheorems.eigenvectors_linear_independent_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:10:24.127166+00:00
-- url     : https://prove2.me/submissions/5007ed1f-1740-4f72-ac65-d3fd29fab3b0

import Mathlib

theorem solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (f : Module.End K V) (μs : Set K)
    (xs : μs → V) (h : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent K xs :=
  Module.End.eigenvectors_linearIndependent f μs xs h
