-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.hasRealEigenvalue_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:18:17.17557+00:00
-- url     : https://prove2.me/submissions/1a621317-8c08-47f3-af36-ee99d1d72ad2

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.hasRealEigenvalue_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (i : Fin n) :
    HasRealEigenvalue T (hT.eigenvalues hn i) := by

  refine ⟨hT.eigenvectorBasis hn i, ?_, hT.apply_eigenvectorBasis hn i⟩
  have hnorm := (hT.eigenvectorBasis hn).orthonormal.1 i
  intro h
  rw [h] at hnorm
  simp at hnorm
