-- Prove2me | solution 1 for BookProof.HermiteRelative.re_inner_diagonal_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:51.363637+00:00
-- url     : https://prove2.me/submissions/1deb9394-3693-4a93-8e5a-343d426bd240

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.re_inner_diagonal_le
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_re_inner_sum_of_diagonal
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
theorem solution (v : ι → E) (hv : Orthonormal ℂ v) (lam mu : ι → ℝ)
    {D : Submodule ℂ E} (hD : Submodule.span ℂ (Set.range v) = D)
    (S T : D →ₗ[ℂ] E)
    (hS : ∀ (a : ι) (h : v a ∈ D), S ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((mu a : ℝ) : ℂ) • v a)
    (hle : ∀ a, lam a ≤ mu a) (u : D) :
    (inner ℂ (u : E) (S u) : ℂ).re ≤ (inner ℂ (u : E) (T u) : ℂ).re := by

  classical
  have hvD : ∀ a, v a ∈ D := fun a => hD ▸ Submodule.subset_span ⟨a, rfl⟩
  have hmem : (u : E) ∈ Submodule.span ℂ (Set.range v) := hD ▸ u.2
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  have hfu : ∑ a ∈ f.support, f a • v a = (u : E) := hf
  have husub : u = ⟨∑ a ∈ f.support, f a • v a, hfu ▸ u.2⟩ := Subtype.ext hfu.symm
  have hS' := re_inner_sum_of_diagonal v hv lam hvD S hS f.support f (hfu ▸ u.2)
  have hT' := re_inner_sum_of_diagonal v hv mu hvD T hT f.support f (hfu ▸ u.2)
  rw [husub, hS', hT']
  exact Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg ‖f a‖, hle a]
