-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:24:43.595951+00:00
-- url     : https://prove2.me/submissions/f4ec1888-b836-4eeb-8867-e6637406c421

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_nonneg
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution {M : Type*} {κ : M → M → ℝ} (hpos : ∀ x : M, 0 ≤ κ x x)
    (π : Fin 3 → M) (B : Fin 3 → Fin 3 → M) :
    0 ≤ weylEnergy κ π B := by

  have h1 : 0 ≤ ∑ i, κ (π i) (π i) := sum_nonneg fun i _ => hpos _
  have h2 : 0 ≤ ∑ i, ∑ j, κ (B i j) (B i j) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => hpos _
  unfold weylEnergy
  linarith
