-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_convolution_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:29.607986+00:00
-- url     : https://prove2.me/submissions/ee2576fe-0cb8-47cd-88eb-11ae7e07340d

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_gradient_convolution_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_integral_inner_convolution_eq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_laplacian_convolution_readable

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Mollification
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Pointwise
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
/-- The Laplacian vanishes outside the closed support. -/
private theorem FunctionalInequalities.KLS.LogConcave.laplacian_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    Laplacian.laplacian f y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = 0 := by
    by_contra h
    exact hy (tsupport_fderiv_subset (𝕜 := ℝ) (support_fderiv_subset (𝕜 := ℝ) h))
  rw [laplacian_eq_sum_fderiv_fderiv, h2]
  simp
variable [CompleteSpace V]
omit [FiniteDimensional ℝ V] in
/-- The gradient vanishes outside the closed support. -/
private theorem FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    gradient f y = 0 := by
  have h : fderiv ℝ f y = 0 := by
    by_contra h
    exact hy (support_fderiv_subset (𝕜 := ℝ) h)
  rw [gradient, h, map_zero]
end Pointwise
section Haar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
/-- **The mollified weak equation.** If `W` satisfies the weak equation
`∫ Δf W = ∫ ⟪∇f, W F⟫ + ∫ f W` against every smooth compactly supported `f`, `η` is a bump equal
to one on `closedBall 0 (R + 1)`, and `ρ` is a normalised bump of radius at most one, then the
mollifications `v = ρ ⋆ (η W)` and `H = ρ ⋆ (η W F)` satisfy the same equation against every
smooth test supported in `closedBall 0 R`. The mollifier is moved onto the test function by the
symmetry identity, commuted with `Δ` and `∇`, and the cutoff `η` is invisible where the mollified
test lives. -/
 theorem solution {W : V → ℝ} {F : V → V}
    (hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ x, Laplacian.laplacian f x * W x ∂m =
        ∫ x, ⟪gradient f x, W x • F x⟫ ∂m + ∫ x, f x * W x ∂m)
    {R : ℝ} (η : ContDiffBump (0 : V)) (hη : R + 1 ≤ η.rIn)
    (hw : Integrable (fun x => η x * W x) m) (hG : Integrable (fun x => (η x * W x) • F x) m)
    (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1) {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgR : tsupport g ⊆ closedBall 0 R) :
    ∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, ⟪gradient g x,
          (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m +
        ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hρloc : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  -- the mollified test function
  set f : V → ℝ := φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g with hf_def
  have hf : ContDiff ℝ ∞ f :=
    HasCompactSupport.contDiff_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
      φ.contDiff_normed hg1.continuous.locallyIntegrable
  have hfc : HasCompactSupport f :=
    HasCompactSupport.convolution _ (φ.hasCompactSupport_normed (μ := m)) hgc
  have hfsupp : tsupport f ⊆ closedBall 0 (R + 1) := by
    refine closure_minimal ?_ isClosed_closedBall
    refine (support_convolution_subset _).trans ?_
    rintro x ⟨a, ha, b, hb, rfl⟩
    rw [φ.support_normed_eq, mem_ball, dist_zero_right] at ha
    have hb' : ‖b‖ ≤ R := by
      have := hgR (subset_tsupport _ hb)
      rwa [mem_closedBall, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_add_le a b]
  have hη1 : ∀ x ∈ tsupport f, η x = 1 := fun x hx =>
    η.one_of_mem_closedBall (closedBall_subset_closedBall hη (hfsupp hx))
  -- the derivatives of the mollified test
  have hlap : ∀ x, Laplacian.laplacian f x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x :=
    FunctionalInequalities.Analysis.Mollification.laplacian_convolution_readable φ hg hgc
  have hgrad : ∀ x, gradient f x = (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x :=
    FunctionalInequalities.Analysis.Mollification.gradient_convolution_readable φ hg hgc
  -- the weak equation for `f`
  have hWf := hW f hf hfc
  -- (i) the Laplacian term
  have e1 : ∫ x, Laplacian.laplacian g x *
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, Laplacian.laplacian f x * W x ∂m := by
    have h := FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_readable (E := ℝ) φ hw (FunctionalInequalities.Analysis.BakryEmery.continuous_laplacian hg2)
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_laplacian hgc)
    simp only [Real.inner_apply] at h
    rw [show (∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m) =
        ∫ x, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x *
          Laplacian.laplacian g x ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← hlap]
    by_cases hx : x ∈ tsupport f
    · rw [hη1 x hx]; ring
    · rw [FunctionalInequalities.KLS.LogConcave.laplacian_eq_zero_of_notMem_tsupport hx]; ring
  -- (ii) the gradient term
  have e2 : ∫ x, ⟪gradient f x, W x • F x⟫ ∂m = ∫ x, ⟪gradient g x,
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m := by
    have h := FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_readable (E := V) φ hG (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hg1)
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hgc)
    rw [show (∫ x, ⟪gradient g x,
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m) =
        ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x,
          gradient g x⟫ ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ tsupport f
    · rw [hgrad, hη1 x hx, one_mul, real_inner_comm]
    · rw [FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport hx, inner_zero_left, ← hgrad,
        FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  -- (iii) the zeroth-order term
  have e3 : ∫ x, f x * W x ∂m =
      ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by
    have h := FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_readable (E := ℝ) φ hw hg1.continuous hgc
    simp only [Real.inner_apply] at h
    rw [show (∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m)
        = ∫ x, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x * g x ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * W x = η x * W x * f x
    by_cases hx : x ∈ tsupport f
    · rw [hη1 x hx]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
  rw [e1, hWf, e2, e3]
