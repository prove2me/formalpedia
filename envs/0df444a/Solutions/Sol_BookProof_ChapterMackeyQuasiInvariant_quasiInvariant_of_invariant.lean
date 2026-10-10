-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:38:03.82189+00:00
-- url     : https://prove2.me/submissions/ec4dd3c4-311e-479e-a744-c75675972282

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_of_invariant
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
open BookProof.ChapterMackeyQuasiInvariant



open MeasureTheory Measure


variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))
variable {μ L}

set_option maxHeartbeats 1000000 in
theorem solution {μ : Measure X}
    (hm : ∀ g : G, Measurable fun x : X => g • x)
    (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) : QuasiInvariant μ G := ⟨hm, fun g => by rw [hinv g]⟩
