-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:06:33.42098+00:00
-- url     : https://prove2.me/submissions/a76d498d-46f3-4c92-b428-c8dd82a1e589

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC (U q) (U k) = coherentOverlapC q k := by

  rw [coherentOverlapC, coherentOverlapC, U.norm_map, U.norm_map, U.inner_map_map]
