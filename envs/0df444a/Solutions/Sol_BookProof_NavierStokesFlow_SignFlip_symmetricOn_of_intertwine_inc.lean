-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.symmetricOn_of_intertwine_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:14:42.042132+00:00
-- url     : https://prove2.me/submissions/3f155ec8-8759-4986-97f0-1a9a5077f53f

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.symmetricOn_of_intertwine_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D) (hUsurj : ∀ v : D, ∃ u : D, U (u : F) = (v : F))
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : SymmetricOn D T) : SymmetricOn D T' := by

  intro x y
  obtain ⟨a, ha⟩ := hUsurj x
  obtain ⟨b, hb⟩ := hUsurj y
  have hx : x = ⟨U (a : F), hU a⟩ := Subtype.ext ha.symm
  have hy : y = ⟨U (b : F), hU b⟩ := Subtype.ext hb.symm
  subst hx
  subst hy
  rw [← hcomm a, ← hcomm b]
  simpa [U.inner_map_map] using hT a b
