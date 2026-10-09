-- Prove2me | solution 1 for BookProof.DensitySpectral.density_spectral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:09.005417+00:00
-- url     : https://prove2.me/submissions/fdbe5f10-8169-493a-bbc4-7979c30480c4

-- Generated from ChapterDensitySpectral.lean — solution of BookProof.DensitySpectral.density_spectral
import Mathlib
import Definitions.Def_ChapterDensitySpectral
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) :
    ρ = (h.1.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (RCLike.ofReal ∘ h.1.eigenvalues)
        * (h.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by

  have hs := h.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  simpa [Matrix.star_eq_conjTranspose] using hs
