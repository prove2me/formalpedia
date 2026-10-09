-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.ext_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T10:23:54.177241+00:00
-- url     : https://prove2.me/submissions/1075434e-dc62-4441-a710-c4eb6cff6c46

-- Generated from ChapterStoneTheorem.lean — solution of BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.ext'
import Mathlib
import Definitions.Def_ChapterStoneTheorem
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup



open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ {G G' : WeakMeasurableUnitaryGroup H}, (∀ t, G.U t = G'.U t) → G = G'
| ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, h => by
      simp only [WeakMeasurableUnitaryGroup.mk.injEq]
      exact funext h
