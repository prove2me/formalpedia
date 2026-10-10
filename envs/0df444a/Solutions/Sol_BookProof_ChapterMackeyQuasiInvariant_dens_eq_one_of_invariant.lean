-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:38:38.097986+00:00
-- url     : https://prove2.me/submissions/73623821-9f26-4283-824e-9ecf3f657d92

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.dens_eq_one_of_invariant
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
theorem solution {μ : Measure X} [SigmaFinite μ]
    (hinv : ∀ g : G, (μ.map fun x : X => g • x) = μ) (g : G) :
    dens μ g =ᵐ[μ] fun _ => 1 := by

  rw [dens, hinv g]
  exact Measure.rnDeriv_self μ
