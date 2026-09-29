-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.eq_zero_of_inner_coreT
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:28.324448+00:00
-- url     : https://prove2.me/submissions/dfb96572-b637-4acf-80fb-13fe8bae6bab

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.eq_zero_of_inner_coreT
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_polyGaussCoreT_dense
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (v : L2d d)
    (h : ∀ z ∈ polyGaussCoreT a k, (inner ℂ z v : ℂ) = 0) : v = 0 := by

  have hclosed : IsClosed {z : L2d d | (inner ℂ z v : ℂ) = 0} := by
    have hcont : Continuous fun z : L2d d => (inner ℂ z v : ℂ) := by fun_prop
    exact isClosed_eq hcont continuous_const
  have hsub : (Set.univ : Set (L2d d)) ⊆ {z : L2d d | (inner ℂ z v : ℂ) = 0} := by
    rw [← (polyGaussCoreT_dense a k).closure_eq]
    exact hclosed.closure_subset_iff.mpr h
  exact inner_self_eq_zero.mp (hsub (Set.mem_univ v))
