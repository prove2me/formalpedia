-- Prove2me | solution 1 for BookProof.QuadraticRotation.eq_zero_of_inner_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:58:30.382935+00:00
-- url     : https://prove2.me/submissions/becc252f-73c7-4f6b-ae97-dbebb4c398a9

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.eq_zero_of_inner_core
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (w : L2d d)
    (h : ∀ u ∈ polyGaussCore (d := d), (inner ℂ u w : ℂ) = 0) : w = 0 := by

  have hclosed : IsClosed {u : L2d d | (inner ℂ u w : ℂ) = 0} := by
    have hcont : Continuous fun u : L2d d => (inner ℂ u w : ℂ) := by fun_prop
    exact isClosed_eq hcont continuous_const
  have hsub : (Set.univ : Set (L2d d)) ⊆ {u : L2d d | (inner ℂ u w : ℂ) = 0} := by
    rw [← (polyGaussCore_dense (d := d)).closure_eq]
    exact hclosed.closure_subset_iff.mpr h
  exact inner_self_eq_zero.mp (hsub (Set.mem_univ w))
