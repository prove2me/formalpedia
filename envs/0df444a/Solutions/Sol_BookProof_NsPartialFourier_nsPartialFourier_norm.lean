-- Prove2me | solution 1 for BookProof.NsPartialFourier.nsPartialFourier_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:56:59.500914+00:00
-- url     : https://prove2.me/submissions/4500b173-2c07-4f77-9ae4-1a247a21f969

import Mathlib
import Definitions.Def_ChapterNsPartialFourier
-- Generated from ChapterNsPartialFourier.lean — theorem BookProof.NsPartialFourier.nsPartialFourier_norm
open BookProof.NsPartialFourier



open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
theorem h43_postcomp_apply {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    (T : F₁ →L[ℂ] G₁) (f : 𝓢(V₁, F₁)) (x : V₁) : BookProof.NsPartialFourier.postcompCLM T f x = T (f x) := by
  simp [BookProof.NsPartialFourier.postcompCLM]

theorem h43_toLp_postcomp {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    (T : F₁ →L[ℂ] G₁) (f : 𝓢(V₁, F₁)) :
    (BookProof.NsPartialFourier.postcompCLM T f).toLp 2 (volume : Measure V₁) = T.compLp (f.toLp 2 (volume : Measure V₁)) := by
  apply Lp.ext
  filter_upwards [SchwartzMap.coeFn_toLp (BookProof.NsPartialFourier.postcompCLM T f) 2 (volume : Measure V₁),
    T.coeFn_compLp (f.toLp 2 (volume : Measure V₁)),
    SchwartzMap.coeFn_toLp f 2 (volume : Measure V₁)] with x h1 h2 h3
  rw [h1, h2, h3, h43_postcomp_apply]

theorem h43_fourier_postcomp_apply {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [CompleteSpace F₁] [CompleteSpace G₁]
    (T : F₁ →L[ℂ] G₁) (f : 𝓢(V₁, F₁)) (x : V₁) :
    (𝓕 (BookProof.NsPartialFourier.postcompCLM T f) : 𝓢(V₁, G₁)) x = T ((𝓕 f : 𝓢(V₁, F₁)) x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have : (⇑(BookProof.NsPartialFourier.postcompCLM T f)) = fun y => T (f y) := funext (h43_postcomp_apply T f)
  rw [this, Real.fourier_eq, Real.fourier_eq]
  have hi := (Real.fourierIntegral_convergent_iff (μ := volume) x).2 (SchwartzMap.integrable f)
  simp_rw [Circle.smul_def] at hi ⊢
  simp_rw [← T.map_smul]
  exact T.integral_comp_comm hi

theorem h43_fourier_postcomp {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [CompleteSpace F₁] [CompleteSpace G₁]
    (T : F₁ →L[ℂ] G₁) (f : 𝓢(V₁, F₁)) :
    (𝓕 (BookProof.NsPartialFourier.postcompCLM T f) : 𝓢(V₁, G₁)) = BookProof.NsPartialFourier.postcompCLM T (𝓕 f : 𝓢(V₁, F₁)) := by
  ext x
  rw [h43_fourier_postcomp_apply, h43_postcomp_apply]

theorem h43_pf_fibre {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [NormedAddCommGroup G₁]
    [InnerProductSpace ℂ G₁] [CompleteSpace F₁] [CompleteSpace G₁]
    (T : F₁ →L[ℂ] G₁) (f : Lp F₁ 2 (volume : Measure V₁)) :
    partialFourier V₁ G₁ (fibreOp V₁ T f) = fibreOp V₁ T (partialFourier V₁ F₁ f) := by
  refine DenseRange.induction_on
    (p := fun f => partialFourier V₁ G₁ (fibreOp V₁ T f) = fibreOp V₁ T (partialFourier V₁ F₁ f))
    (SchwartzMap.denseRange_toLpCLM (F := F₁) (p := 2) (μ := (volume : Measure V₁))
      ENNReal.ofNat_ne_top) f ?_ ?_
  · exact isClosed_eq ((partialFourier V₁ G₁).continuous.comp (fibreOp V₁ T).continuous)
      ((fibreOp V₁ T).continuous.comp (partialFourier V₁ F₁).continuous)
  · intro g
    simp only [SchwartzMap.toLpCLM_apply]
    have e1 : ∀ h : 𝓢(V₁, F₁), fibreOp V₁ T (h.toLp 2 (volume : Measure V₁))
        = (BookProof.NsPartialFourier.postcompCLM T h).toLp 2 (volume : Measure V₁) := fun h =>
      (h43_toLp_postcomp T h).symm
    have e2F : partialFourier V₁ F₁ (g.toLp 2 (volume : Measure V₁)) = (𝓕 g).toLp 2 (volume : Measure V₁) :=
      SchwartzMap.toLp_fourier_eq g
    have e2G : partialFourier V₁ G₁ ((BookProof.NsPartialFourier.postcompCLM T g).toLp 2 (volume : Measure V₁))
        = (𝓕 (BookProof.NsPartialFourier.postcompCLM T g)).toLp 2 (volume : Measure V₁) :=
      SchwartzMap.toLp_fourier_eq _
    rw [e1, e2G, e2F, e1, h43_fourier_postcomp]

theorem h43_postcomp_lineDeriv {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    (T : F₁ →L[ℂ] G₁) (f : 𝓢(V₁, F₁)) (m : V₁) :
    BookProof.NsPartialFourier.postcompCLM T (∂_{m} f : 𝓢(V₁, F₁)) = (∂_{m} (BookProof.NsPartialFourier.postcompCLM T f) : 𝓢(V₁, G₁)) := by
  ext x
  rw [h43_postcomp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have : (⇑(BookProof.NsPartialFourier.postcompCLM T f)) = fun y => T (f y) := funext (h43_postcomp_apply T f)
  rw [this]
  have h := ((T.restrictScalars ℝ).hasFDerivAt.comp x (f.differentiableAt.hasFDerivAt)).fderiv
  change _ = fderiv ℝ ((T.restrictScalars ℝ) ∘ f) x m
  rw [h]; rfl

theorem h43_postcomp_vecMom {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    [NormedAddCommGroup G₁] [InnerProductSpace ℂ G₁] [CompleteSpace G₁]
    (T : F₁ →L[ℂ] G₁) (m : V₁) (f : 𝓢(V₁, F₁)) :
    BookProof.NsPartialFourier.postcompCLM T (vecMomentumOp m f) = vecMomentumOp m (BookProof.NsPartialFourier.postcompCLM T f) := by
  simp only [vecMomentumOp, ContinuousLinearMap.smul_apply, lineDerivOpCLM_apply, map_smul,
    h43_postcomp_lineDeriv]

theorem h43_fourier_vecMom_apply {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [FiniteDimensional ℝ V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    (m : V₁) (f : 𝓢(V₁, F₁)) (x : V₁) :
    (𝓕 (vecMomentumOp m f) : 𝓢(V₁, F₁)) x
      = ((2 * Real.pi * (inner ℝ x m) : ℝ) : ℂ) • (𝓕 f : 𝓢(V₁, F₁)) x := by
  have ht : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp only [vecMomentumOp, ContinuousLinearMap.smul_apply, lineDerivOpCLM_apply, FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht]
  rw [← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem solution (v : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :
    ‖nsPartialFourier V W v‖ = ‖v‖ := by
  exact (nsPartialFourier V W).norm_map v

