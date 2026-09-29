-- Prove2me | solution 1 for FamousTheorems.generalized_eigenspace_decomposition_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:10:40.728496+00:00
-- url     : https://prove2.me/submissions/63222d9a-993b-4493-9348-3fdce75377ff

import Mathlib

theorem solution {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) : ⨆ μ : K, f.maxGenEigenspace μ = ⊤ :=
  Module.End.iSup_maxGenEigenspace_eq_top f
