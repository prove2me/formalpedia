-- Prove2me | solution 1 for BookProof.ClosureUniqueness.factorGraph_eq_of_clGraph_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:18:52.128989+00:00
-- url     : https://prove2.me/submissions/6d49fd5a-71b2-49a7-809d-d6ddacaa14ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.factorGraph_eq_of_clGraph_eq
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_of_clGraph_eq
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h : clGraph T₁ = clGraph T₂) : factorGraph T₁ = factorGraph T₂ := by

  have hadj : adjGraph T₁ = adjGraph T₂ := adjGraph_eq_of_clGraph_eq h
  exact Set.ext fun p => exists_congr fun y =>
    and_congr (by rw [h]) (by rw [hadj])
