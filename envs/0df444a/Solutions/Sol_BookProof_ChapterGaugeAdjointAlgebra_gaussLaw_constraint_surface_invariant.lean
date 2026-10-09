-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:23:52.135078+00:00
-- url     : https://prove2.me/submissions/50d286ee-ddb0-4bcd-9dfb-26900a133092

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
import Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_gaussLaw_covariant
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution (A dπ π : Fin 3 → L) (θ : L)
    (hG : gaussLaw A dπ π = 0) :
    ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆)) = 0 := by

  rw [gaussLaw_covariant, hG, zero_lie]
