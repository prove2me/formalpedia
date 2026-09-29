-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.repr_apply_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:22:40.789743+00:00
-- url     : https://prove2.me/submissions/9c0dce97-439c-460c-8721-3e0d396faf36

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.repr_apply_of_symmetric
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
    (hn : Module.finrank ℂ E = n) (x : E) (i : Fin n) :
    coeff hT hn (T x) i = (hT.eigenvalues hn i : ℂ) * coeff hT hn x i := by

  rw [coeff, coeff, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    ← hT, hT.apply_eigenvectorBasis hn i, inner_smul_left]
  simp
