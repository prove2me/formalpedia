-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.variance_le_sum_of_partial_dual_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:24:18.920993+00:00
-- url     : https://prove2.me/submissions/e111400e-5383-494d-a3be-9b54aa0befa8

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_centered_mem_closure_compactSmoothDiffusionImage_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_compact_pairing_identity_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_inner_center_left_of_mean_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_sq_le_of_mem_closure_quadratic_bound_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem FunctionalInequalities.L2.coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem FunctionalInequalities.L2.coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]
/-- Taking the mean commutes with embedding a pointwise square-integrable function into `L²`. -/
theorem FunctionalInequalities.L2.mean_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    mean μ (hf.toLp f) = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean_eq_integral]
  exact integral_congr_ae hf.coeFn_toLp
end
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end

section
noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Every centered representative, including an arbitrary input after centering, has the same approximation property. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_mem_closure_compactSmoothDiffusionImage
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (g : Lp ℝ 2 (ν : Measure V)) :
    L2.center ν g ∈ closure (compactSmoothDiffusionImage hU) := by
  exact centered_mem_closure_compactSmoothDiffusionImage_readable m hν hνU hU
    (L2.center ν g) (L2.mean_center ν g)
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
section RealL2
variable {α : Type*} [MeasurableSpace α]
/-- The scalar pairing of actual `toLp` classes is the integral of the
product of their original functions. -/
theorem FunctionalInequalities.KLS.LogConcave.real_inner_toLp {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]
end RealL2
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [SecondCountableTopology E] in
/-- Every literal compact smooth diffusion image has mean zero, by compact
integration by parts against the constant function one. -/
theorem FunctionalInequalities.KLS.LogConcave.compact_diffusion_toLp_mean_zero
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    FunctionalInequalities.L2.mean ν
      ((memLp_neg_weightedLaplacian (ν := ν) hU hu huc).toLp
        (fun x => -weightedLaplacian U u x)) = 0 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hibp := integral_inner_gradient_tilted m
    (g := fun _ : E => (1 : ℝ)) hU hu2 huc contDiff_const
  rw [← hνU] at hibp
  rw [FunctionalInequalities.L2.mean_toLp]
  simpa only [gradient_fun_const, inner_zero_right, integral_zero, mul_one]
    using hibp.symm
end FiniteDimensional
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
section LT9DHminus1VarianceAssembly
open ProbabilityTheory InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped RealInnerProductSpace
/-- **`H⁻¹` variance bound for a convex potential** (Letwin arXiv:2607.24164v1, Proposition 2.8,
quoted from Barthe–Klartag; here for a `C²` convex potential, the form used after Gaussian
smoothing of the target): if `ν = e^{-W} dm` with `W` convex and `C²`, `f ∈ C¹ ∩ L²(ν)` has square
integrable partial derivatives, and each partial derivative satisfies the dual bound
`(∫ ∂ᵢf · h dν)² ≤ Kᵢ ∫ ‖∇h‖² dν` for all compactly supported smooth `h`, then
`Var_ν f ≤ Σᵢ Kᵢ`. -/
theorem solution {n : ℕ}
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hν : FunctionalInequalities.KLS.LogConcave ν)
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
    (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ Set.univ W)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (ν : Measure _))
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (ν : Measure _))
    (K : Fin n → ℝ)
    (hK : ∀ i (h : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure _)) ^ 2 ≤
        K i * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    variance f (ν : Measure _) ≤ ∑ i, K i := by
  have _ := hdf2
  have hU1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  let F : Lp ℝ 2 (ν : Measure _) := hf2.toLp f
  let C : ℝ := ∑ i, K i
  have hKnonneg : ∀ i, 0 ≤ K i := by
    intro i
    exact FunctionalInequalities.KLS.LogConcave.nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_readable
      (Fin.pos i) m hνW hW.continuous (hK i)
  have hQ : ∀ w ∈ FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage (ν := ν) hU1,
      2 * ⟪FunctionalInequalities.L2.center ν F, w⟫ - ‖w‖ ^ 2 ≤ C := by
    rintro w ⟨g, hg, hgc, rfl⟩
    let hL : MemLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x) 2 (ν : Measure _) :=
      FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := ν) hU1 hg hgc
    let G : Lp ℝ 2 (ν : Measure _) :=
      hL.toLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x)
    change 2 * ⟪FunctionalInequalities.L2.center ν F, G⟫ - ‖G‖ ^ 2 ≤ C
    have hmean : FunctionalInequalities.L2.mean ν G = 0 :=
      FunctionalInequalities.KLS.LogConcave.compact_diffusion_toLp_mean_zero m hνW hU1 hg hgc
    have hinner : ⟪F, G⟫ =
        ∫ x, f x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x) ∂(ν : Measure _) :=
      FunctionalInequalities.KLS.LogConcave.real_inner_toLp hf2 hL
    have hnorm : ‖G‖ ^ 2 =
        ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x ^ 2 ∂(ν : Measure _) := by
      simpa only [G, Real.norm_eq_abs, abs_neg, sq_abs] using
        (FunctionalInequalities.L2.norm_toLp_sq hL)
    obtain ⟨_, _, hpair⟩ :=
      FunctionalInequalities.KLS.LogConcave.compact_pairing_identity_readable m hνW hU1 hf hg hgc
    have hcoord_f (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
        (gradient f x).ofLp i =
          fderiv ℝ f x (EuclideanSpace.single i 1) := by
      calc
        (gradient f x).ofLp i =
            inner ℝ (gradient f x) (EuclideanSpace.single i 1) := by
          simpa using
            (EuclideanSpace.inner_single_right i (1 : ℝ) (gradient f x)).symm
        _ = fderiv ℝ f x (EuclideanSpace.single i 1) := by
          simpa only [gradient] using
            (InnerProductSpace.toDual_symm_apply
              (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
              (x := EuclideanSpace.single i 1) (y := fderiv ℝ f x))
    have hcoord_g (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
        (gradient g x).ofLp i =
          fderiv ℝ g x (EuclideanSpace.single i 1) := by
      calc
        (gradient g x).ofLp i =
            inner ℝ (gradient g x) (EuclideanSpace.single i 1) := by
          simpa using
            (EuclideanSpace.inner_single_right i (1 : ℝ) (gradient g x)).symm
        _ = fderiv ℝ g x (EuclideanSpace.single i 1) := by
          simpa only [gradient] using
            (InnerProductSpace.toDual_symm_apply
              (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
              (x := EuclideanSpace.single i 1) (y := fderiv ℝ g x))
    let A : Fin n → ℝ := fun i =>
      ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) *
        fderiv ℝ g x (EuclideanSpace.single i 1) ∂(ν : Measure _)
    let D : Fin n → ℝ := fun i =>
      ∫ x, ‖fderiv ℝ (fun y =>
        fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2 ∂(ν : Measure _)
    have hprod_int (i : Fin n) :
        Integrable (fun x =>
          fderiv ℝ f x (EuclideanSpace.single i 1) *
            fderiv ℝ g x (EuclideanSpace.single i 1)) (ν : Measure _) := by
      have hp :
          Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
            (x, EuclideanSpace.single i (1 : ℝ))) :=
        Continuous.prodMk continuous_id continuous_const
      have hfc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ f x (EuclideanSpace.single i 1)) := by
        simpa only [Function.comp_def] using
          (hf.continuous_fderiv_apply (by simp)).comp hp
      have hgccont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ g x (EuclideanSpace.single i 1)) := by
        simpa only [Function.comp_def] using
          (hg.continuous_fderiv_apply (by simp)).comp hp
      have hgc' : HasCompactSupport (fun x =>
          fderiv ℝ g x (EuclideanSpace.single i 1)) := by
        simpa only [Function.comp_def] using
          (hgc.fderiv ℝ).comp_left
            (g := fun q => q (EuclideanSpace.single i 1)) (by simp)
      exact (hfc.mul hgccont).integrable_of_hasCompactSupport hgc'.mul_left
    have hgrad_sum :
        (∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure _)) =
          ∑ i, A i := by
      calc
        (∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure _)) =
            ∫ x, ∑ i, fderiv ℝ f x (EuclideanSpace.single i 1) *
              fderiv ℝ g x (EuclideanSpace.single i 1) ∂(ν : Measure _) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [PiLp.inner_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoord_f i x, hcoord_g i x]
          simp [mul_comm]
        _ = ∑ i, A i := by
          rw [MeasureTheory.integral_finsetSum]
          intro i hi
          exact hprod_int i
    have hterm : ∀ i, 2 * A i ≤ K i + D i := by
      intro i
      have hsq := hK i
        (fun x => fderiv ℝ g x (EuclideanSpace.single i 1))
        (by
          have hp :
              ContDiff ℝ ∞
                (fun x : EuclideanSpace ℝ (Fin n) =>
                  (x, EuclideanSpace.single i (1 : ℝ))) :=
            contDiff_id.prodMk contDiff_const
          simpa only [Function.comp_def] using
            (hg.contDiff_fderiv_apply (m := ∞) (by simp)).comp hp)
        (by
          simpa only [Function.comp_def] using
            (hgc.fderiv ℝ).comp_left
              (g := fun q => q (EuclideanSpace.single i 1)) (by simp))
      change
        2 * (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) *
          fderiv ℝ g x (EuclideanSpace.single i 1) ∂(ν : Measure _)) ≤
          K i + ∫ x, ‖fderiv ℝ
            (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
            ∂(ν : Measure _)
      have hD : 0 ≤ ∫ x, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
          ∂(ν : Measure _) :=
        integral_nonneg (fun x => sq_nonneg _)
      nlinarith [hsq, hKnonneg i, hD, sq_nonneg
        (K i - ∫ x, ‖fderiv ℝ
          (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x‖ ^ 2
          ∂(ν : Measure _))]
    have hsum :
        2 * ∑ i, A i ≤ ∑ i, K i + ∑ i, D i := by
      have h :=
        Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
          (fun i hi => hterm i)
      simpa [Finset.mul_sum, Finset.sum_add_distrib] using h
    have hLT9c := FunctionalInequalities.Analysis.BakryEmery.sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq_readable
      m hW hWc hg hgc
    rw [← hνW] at hLT9c
    have hLT9c' :
        ∑ i, D i ≤
          ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x ^ 2 ∂(ν : Measure _) := by
      simpa [D] using hLT9c
    have hmain :
        2 * ∑ i, A i -
            ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x ^ 2 ∂(ν : Measure _) ≤ C := by
      change
        2 * ∑ i, A i -
            ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W g x ^ 2 ∂(ν : Measure _) ≤ ∑ i, K i
      linarith
    rw [FunctionalInequalities.KLS.LogConcave.inner_center_left_of_mean_zero_readable ν F G hmean, hinner, hnorm, hpair,
      hgrad_sum]
    exact hmain
  have hclosure : FunctionalInequalities.L2.center ν F ∈
      closure (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage (ν := ν) hU1) :=
    FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_mem_closure_compactSmoothDiffusionImage m hν hνW hU1 F
  have hnorm : ‖FunctionalInequalities.L2.center ν F‖ ^ 2 ≤ C :=
    FunctionalInequalities.KLS.LogConcave.norm_sq_le_of_mem_closure_quadratic_bound_readable
      (FunctionalInequalities.L2.center ν F) hclosure hQ
  have hvariance : (FunctionalInequalities.L2.variance ν F : ℝ) =
      variance f (ν : Measure _) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise ν F).trans
      (variance_congr hf2.coeFn_toLp)
  rw [← hvariance, FunctionalInequalities.L2.coe_variance]
  exact hnorm
