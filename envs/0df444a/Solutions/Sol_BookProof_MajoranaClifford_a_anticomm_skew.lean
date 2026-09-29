-- Prove2me | solution 1 for BookProof.MajoranaClifford.a_anticomm_skew
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:38:51.051862+00:00
-- url     : https://prove2.me/submissions/4e5bea97-b3e7-46b1-b3cd-7e39890e4f30

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.a_anticomm_skew
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
import Theorems.Thm_BookProof_MajoranaClifford_a_anticomm_of_orthogonal
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (J : V →ₗ[ℝ] V) (hJ : ∀ v w : V, ⟪J v, w⟫ = -⟪v, J w⟫) (v : V) :
    a v * a (J v) + a (J v) * a v = 0 := by

  have h : ⟪v, J v⟫ = (0 : ℝ) := by
    have h1 : ⟪J v, v⟫ = -⟪v, J v⟫ := hJ v v
    have h2 : ⟪J v, v⟫ = ⟪v, J v⟫ := by rw [real_inner_comm]
    linarith [h1, h2]
  exact a_anticomm_of_orthogonal h
