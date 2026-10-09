-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.lie_adj_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:23:13.491236+00:00
-- url     : https://prove2.me/submissions/b037fdcc-3ed2-4300-8d79-e0ed1998e6ce

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.lie_adj_leibniz
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution (x θ y : L) : ⁅⁅x, θ⁆, y⁆ + ⁅x, ⁅y, θ⁆⁆ = ⁅⁅x, y⁆, θ⁆ := by

  rw [lie_lie x y θ, ← lie_skew ⁅x, θ⁆ y]
  abel
