-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:23:51.14339+00:00
-- url     : https://prove2.me/submissions/07fbb703-4a0b-453c-b102-049db0d76573

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
import Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_lie_adj_leibniz
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution (A dπ π : Fin 3 → L) (θ : L) :
    ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆))
      = ⁅gaussLaw A dπ π, θ⁆ := by

  simp only [gaussLaw, sum_lie, add_lie]
  exact sum_congr rfl fun i _ => by rw [lie_adj_leibniz (A i) θ (π i)]
