-- Prove2me | solution 1 for BookProof.HermiteRelative.re_inner_sum_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:16.691681+00:00
-- url     : https://prove2.me/submissions/9d8747e2-585a-424d-9347-74c27ad91c08

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.re_inner_sum_of_diagonal
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_apply_sum_of_diagonal
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
open BookProof.HermiteRelative










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (v : ι → E) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    {D : Submodule ℂ E} (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (s : Finset ι) (f : ι → ℂ) (hu : (∑ a ∈ s, f a • v a) ∈ D) :
    (inner ℂ (∑ a ∈ s, f a • v a) (T ⟨∑ a ∈ s, f a • v a, hu⟩) : ℂ).re
      = ∑ a ∈ s, lam a * ‖f a‖ ^ 2 := by

  rw [apply_sum_of_diagonal v lam hvD T hT s f hu,
    hv.inner_sum f (fun a => ((lam a : ℝ) : ℂ) * f a) s, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (starRingEnd ℂ) (f a) * (((lam a : ℝ) : ℂ) * f a)
      = ((lam a : ℝ) : ℂ) * (f a * (starRingEnd ℂ) (f a)) := by ring
  rw [h, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
