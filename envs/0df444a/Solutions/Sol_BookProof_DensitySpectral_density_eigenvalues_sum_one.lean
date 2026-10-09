-- Prove2me | solution 1 for BookProof.DensitySpectral.density_eigenvalues_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:04.797074+00:00
-- url     : https://prove2.me/submissions/89377ac2-e06c-4964-b0af-6d96d1e40833

-- Generated from ChapterDensitySpectral.lean — solution of BookProof.DensitySpectral.density_eigenvalues_sum_one
import Mathlib
import Definitions.Def_ChapterDensitySpectral
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) :
    ∑ i, h.1.eigenvalues i = 1 := by

  have htr : ρ.trace = ∑ i, ((h.1.eigenvalues i : ℝ) : ℂ) := h.1.trace_eq_sum_eigenvalues
  have hsum : ∑ i, ((h.1.eigenvalues i : ℝ) : ℂ) = 1 := htr.symm.trans h.2.2
  have hcast : ((∑ i, h.1.eigenvalues i : ℝ) : ℂ) = 1 := by rw [Complex.ofReal_sum]; exact hsum
  exact_mod_cast hcast
