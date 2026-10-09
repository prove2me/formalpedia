-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:23:26.190336+00:00
-- url     : https://prove2.me/submissions/c4f23411-703b-4dc6-9ed8-37e1b0e288fc

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution {X : L} (hX : ∀ θ : L, ⁅X, θ⁆ = 0) (θ : L) :
    adjVar θ X = 0 := hX θ
