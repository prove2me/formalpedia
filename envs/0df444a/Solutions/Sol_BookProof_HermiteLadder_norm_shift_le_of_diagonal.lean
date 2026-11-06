-- Prove2me | solution 1 for BookProof.HermiteLadder.norm_shift_le_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T19:48:03.642212+00:00
-- url     : https://prove2.me/submissions/4ea3107d-4b52-4a4d-9fcc-645e0c0f6b5d

-- Generated from ChapterHermiteLadderShift.lean — solution of BookProof.HermiteLadder.norm_shift_le_of_diagonal
import Mathlib
import Definitions.Def_ChapterHermiteLadderShift
import Theorems.Thm_BookProof_HermiteLadder_norm_sum_shift_sq
import Theorems.Thm_BookProof_HermiteLadder_apply_sum_of_shift
import Theorems.Thm_BookProof_HermiteRelative_apply_sum_of_diagonal
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteLadderOrder
open BookProof.HermiteLadder




open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QgHermiteOscillator
open BookProof.HyperbolicQuadratic

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (v : ι → E) (hv : Orthonormal ℂ v) {D : Submodule ℂ E}
    (hD : Submodule.span ℂ (Set.range v) = D)
    (T : D →ₗ[ℂ] E) (σ : ι → ι) (s : ι → ℂ)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = s a • v (σ a))
    (hinj : ∀ a b : ι, s a ≠ 0 → s b ≠ 0 → σ a = σ b → a = b)
    (N : D →ₗ[ℂ] E) (w : ι → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hN : ∀ (a : ι) (h : v a ∈ D), N ⟨v a, h⟩ = ((w a : ℝ) : ℂ) • v a)
    (K : ℝ) (hK : 0 ≤ K) (hs : ∀ a, ‖s a‖ ≤ K * (w a + 1)) (u : D) :
    ‖T u‖ ≤ K * ‖N u + (u : E)‖ := by

  classical
  have hvD : ∀ a, v a ∈ D := fun a => hD ▸ Submodule.subset_span ⟨a, rfl⟩
  have hmem : (u : E) ∈ Submodule.span ℂ (Set.range v) := hD ▸ u.2
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  have hfu : ∑ a ∈ f.support, f a • v a = (u : E) := hf
  have husub : u = ⟨∑ a ∈ f.support, f a • v a, hfu ▸ u.2⟩ := Subtype.ext hfu.symm
  -- the image of `u`
  have hTu : T u = ∑ a ∈ f.support, (f a * s a) • v (σ a) := by
    rw [husub]
    exact apply_sum_of_shift v σ s hvD T hT f.support f _
  -- the shifted diagonal image of `u`
  have hNu : N u + (u : E) = ∑ a ∈ f.support, (f a * ((w a + 1 : ℝ) : ℂ)) • v a := by
    have h1 : N u = ∑ a ∈ f.support, (((w a : ℝ) : ℂ) * f a) • v a := by
      rw [husub]
      exact apply_sum_of_diagonal v w hvD N hN f.support f _
    rw [h1]
    have h2 : (u : E) = ∑ a ∈ f.support, f a • v a := hfu.symm
    rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← add_smul]
    congr 1
    push_cast
    ring
  -- Pythagoras on both sides
  set S₀ : Finset ι := f.support.filter (fun a => s a ≠ 0) with hS₀
  have hdrop : ∑ a ∈ f.support, (f a * s a) • v (σ a)
      = ∑ a ∈ S₀, (f a * s a) • v (σ a) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro a ha hna
    have hs0 : s a = 0 := by
      by_contra hne
      exact hna (Finset.mem_filter.mpr ⟨ha, hne⟩)
    simp [hs0]
  have hnormT : ‖T u‖ ^ 2 = ∑ a ∈ S₀, ‖f a * s a‖ ^ 2 := by
    rw [hTu, hdrop]
    refine norm_sum_shift_sq v hv σ S₀ ?_ _
    intro a ha b hb hab
    exact hinj a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hnormN : ‖N u + (u : E)‖ ^ 2 = ∑ a ∈ f.support, ‖f a * ((w a + 1 : ℝ) : ℂ)‖ ^ 2 := by
    rw [hNu]
    exact norm_sum_shift_sq v hv id f.support (fun a _ b _ h => h) _
  have hle : ∑ a ∈ S₀, ‖f a * s a‖ ^ 2
      ≤ K ^ 2 * ∑ a ∈ f.support, ‖f a * ((w a + 1 : ℝ) : ℂ)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => by positivity)) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ‖f a * s a‖ ^ 2 = ‖f a‖ ^ 2 * ‖s a‖ ^ 2 := by
      rw [norm_mul]; ring
    have h2 : ‖f a * ((w a + 1 : ℝ) : ℂ)‖ ^ 2 = ‖f a‖ ^ 2 * (w a + 1) ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hw a])]
      ring
    rw [h1, h2]
    have hsa := hs a
    have hnn : (0 : ℝ) ≤ ‖f a‖ ^ 2 := by positivity
    have hsq : ‖s a‖ ^ 2 ≤ K ^ 2 * (w a + 1) ^ 2 := by
      have h0 : 0 ≤ ‖s a‖ := norm_nonneg _
      have h1' : 0 ≤ K * (w a + 1) := by
        have := hw a; positivity
      nlinarith [hsa]
    nlinarith [hnn, hsq]
  have hfin : ‖T u‖ ^ 2 ≤ (K * ‖N u + (u : E)‖) ^ 2 := by
    rw [hnormT, mul_pow]
    calc ∑ a ∈ S₀, ‖f a * s a‖ ^ 2
        ≤ K ^ 2 * ∑ a ∈ f.support, ‖f a * ((w a + 1 : ℝ) : ℂ)‖ ^ 2 := hle
      _ = K ^ 2 * ‖N u + (u : E)‖ ^ 2 := by rw [hnormN]
  have h1 : 0 ≤ K * ‖N u + (u : E)‖ := by positivity
  nlinarith [norm_nonneg (T u), hfin]
