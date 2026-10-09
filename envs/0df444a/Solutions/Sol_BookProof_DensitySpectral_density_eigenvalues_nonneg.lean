-- Prove2me | solution 1 for BookProof.DensitySpectral.density_eigenvalues_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:41:48.324038+00:00
-- url     : https://prove2.me/submissions/14eb5358-c20b-42ee-9e98-cd57a60cd287

-- Generated from ChapterDensitySpectral.lean — solution of BookProof.DensitySpectral.density_eigenvalues_nonneg
import Mathlib
import Definitions.Def_ChapterDensitySpectral
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) (i : n) :
    0 ≤ h.1.eigenvalues i := h.2.1.eigenvalues_nonneg i
