-- Prove2me | solution 1 for BookProof.DensitySpectral.density_iff_exists_unitary_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:17.906858+00:00
-- url     : https://prove2.me/submissions/69e86893-c78f-492f-bac9-e8d6976faf68

-- Generated from ChapterDensitySpectral.lean — solution of BookProof.DensitySpectral.density_iff_exists_unitary_diagonal
import Mathlib
import Definitions.Def_ChapterDensitySpectral
import Theorems.Thm_BookProof_DensitySpectral_density_eigenvalues_nonneg
import Theorems.Thm_BookProof_DensitySpectral_density_eigenvalues_sum_one
import Theorems.Thm_BookProof_DensitySpectral_density_spectral
import Theorems.Thm_BookProof_DensitySpectral_isDensityMatrix_of_unitary_diagonal
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (ρ : Matrix n n ℂ) :
    IsDensityMatrix ρ ↔
      ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ),
        (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
        ρ = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d) * (U : Matrix n n ℂ)ᴴ := by

  constructor
  · intro h
    exact ⟨h.1.eigenvectorUnitary, h.1.eigenvalues, density_eigenvalues_nonneg h,
      density_eigenvalues_sum_one h, density_spectral h⟩
  · rintro ⟨U, d, hd, hsum, rfl⟩
    exact isDensityMatrix_of_unitary_diagonal U d hd hsum
