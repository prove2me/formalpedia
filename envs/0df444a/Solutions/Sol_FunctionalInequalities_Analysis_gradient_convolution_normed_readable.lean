-- Prove2me | solution 1 for FunctionalInequalities.Analysis.gradient_convolution_normed_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:24:59.828127+00:00
-- url     : https://prove2.me/submissions/7fe02df2-a24b-4d26-a258-9004cbb9c0ee

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Hessian

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.integrable_mul_of_compact_support
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace E]
    {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) :
    Integrable (fun x => f x * g x) μ := by
  apply (hf.mul hg).integrable_of_hasCompactSupport
  refine hcf.mono ?_
  intro x hx
  by_contra hfx
  have hfx' : f x = 0 := by
    simpa [Function.mem_support] using hfx
  have hzero : (f * g) x = 0 := by
    simp only [Pi.mul_apply, hfx', zero_mul]
  exact hx hzero
private lemma FunctionalInequalities.Analysis.integrable_smul_of_compact_support
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) :
    Integrable (fun x => f x • g x) μ := by
  apply (hf.smul hg).integrable_of_hasCompactSupport
  refine hcf.mono ?_
  intro x hx
  by_contra hfx
  have hfx' : f x = 0 := by
    simpa [Function.mem_support] using hfx
  have hzero : f x • g x = 0 := by
    simp only [hfx', zero_smul]
  exact hx hzero
private lemma FunctionalInequalities.Analysis.continuous_clm_apply
    {f : E → E →L[ℝ] ℝ} (hf : Continuous f) (v : E) :
    Continuous (fun x => f x v) := by
  have hev : Continuous (fun L : E →L[ℝ] ℝ => L v) := by
    fun_prop
  exact hev.comp hf
end NormedSpace
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 lemma solution
    {U : E → ℝ} (hU : ContDiff ℝ 1 U)
    {G : NNReal} (hG : LipschitzWith G (gradient U))
    (φ : ContDiffBump (0 : E)) :
    gradient
        (convolution
          (φ.normed (volume : Measure E)) U
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)) =
      convolution
        (φ.normed (volume : Measure E)) (gradient U)
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) := by
  classical
  let f : E → ℝ := φ.normed (volume : Measure E)
  have hf1 : ContDiff ℝ 1 f := by
    simpa [f] using (φ.contDiff_normed (n := 1))
  have hcf : HasCompactSupport f := by
    simpa [f] using φ.hasCompactSupport_normed
  have hUloc : LocallyIntegrable U (volume : Measure E) :=
    hU.continuous.locallyIntegrable
  have hfd : Continuous (fderiv ℝ f) :=
    hf1.continuous_fderiv (by norm_num)
  have hcfderiv : HasCompactSupport (fderiv ℝ f) :=
    hcf.fderiv ℝ
  funext x
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hd :=
    HasCompactSupport.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      hcf hf1 hUloc x
  rw [hd.fderiv]
  let q : E → E →L[ℝ] ℝ := fun t =>
    U (x - t) • fderiv ℝ f t
  have hqcont : Continuous q := by
    fun_prop
  have hqcf : HasCompactSupport q := by
    refine hcfderiv.mono ?_
    intro t ht
    by_contra hft
    have hft' : fderiv ℝ f t = 0 := by
      simpa [Function.mem_support] using hft
    have hzero : q t = 0 := by
      simp only [q, hft', smul_zero]
    exact ht hzero
  have hqint : Integrable q (volume : Measure E) :=
    hqcont.integrable_of_hasCompactSupport hqcf
  have hgradint :
      Integrable
        (fun t : E => f t • gradient U (x - t))
        (volume : Measure E) := by
    apply FunctionalInequalities.Analysis.integrable_smul_of_compact_support
    · exact φ.continuous_normed
    · exact (LipschitzWith.continuous hG).comp
        (continuous_const.sub continuous_id)
    · exact hcf
  simp only [convolution_def]
  have hleft :
      (∫ t : E,
        ((ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ))
          (fderiv ℝ f t)) (U (x - t)) ∂(volume : Measure E)) =
        ∫ t : E, q t ∂(volume : Measure E) := by
    apply integral_congr_ae
    filter_upwards [] with t
    ext w
    change
      (fderiv ℝ f t) w * U (x - t) =
        U (x - t) * (fderiv ℝ f t) w
    ring
  rw [hleft]
  rw [ContinuousLinearMap.integral_apply hqint v]
  have hconvint :
      Integrable
        (fun t : E =>
          ((ContinuousLinearMap.lsmul ℝ ℝ)
            (φ.normed (volume : Measure E) t)) (gradient U (x - t)))
        (volume : Measure E) := by
    simpa [f, ContinuousLinearMap.lsmul_apply] using hgradint
  rw [real_inner_comm]
  rw [← integral_inner hconvint v]
  let g : E → ℝ := fun s => U (x - s)
  have htrans : ∀ s : E, (fderiv ℝ g s) v = -((fderiv ℝ U (x - s)) v) := by
    intro s
    have ht :
        HasFDerivAt (fun z : E => x - z)
          (-ContinuousLinearMap.id ℝ E) s := by
      convert
        (hasFDerivAt_const (x := s) x).sub (hasFDerivAt_id s) using 1 <;>
        ext z <;> simp
    have hcomp :=
      (hU.differentiable (by norm_num) (x - s)).hasFDerivAt.comp s ht
    have hg : g = U ∘ HSub.hSub x := by
      funext z
      rfl
    rw [hg]
    simpa using congrArg (fun L => L v) hcomp.fderiv
  have h₁ :
      Integrable
        (fun s : E => (fderiv ℝ f s) v * g s)
        (volume : Measure E) := by
    apply FunctionalInequalities.Analysis.integrable_mul_of_compact_support
    · exact FunctionalInequalities.Analysis.continuous_clm_apply hfd v
    · exact hU.continuous.comp (continuous_const.sub continuous_id)
    · refine hcfderiv.mono ?_
      intro s hs
      by_contra hnot
      have hz : fderiv ℝ f s = 0 := by
        simpa [Function.mem_support] using hnot
      exact hs (by simp [hz])
  have h₂ :
      Integrable
        (fun s : E => f s * (fderiv ℝ g s) v)
        (volume : Measure E) := by
    apply FunctionalInequalities.Analysis.integrable_mul_of_compact_support
    · exact hf1.continuous
    · have hUg : Continuous (fderiv ℝ U) :=
        hU.continuous_fderiv (by norm_num)
      have hscalar :
          Continuous (fun s : E => (fderiv ℝ U (x - s)) v) :=
        FunctionalInequalities.Analysis.continuous_clm_apply
          (hUg.comp (continuous_const.sub continuous_id)) v
      have hneg : Continuous (fun s : E => -((fderiv ℝ U (x - s)) v)) :=
        continuous_neg.comp hscalar
      simpa only [htrans] using hneg
    · exact hcf
  have h₃ :
      Integrable (fun s : E => f s * g s) (volume : Measure E) := by
    apply FunctionalInequalities.Analysis.integrable_mul_of_compact_support
    · exact hf1.continuous
    · exact hU.continuous.comp (continuous_const.sub continuous_id)
    · exact hcf
  have hi :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      h₁ h₂ h₃
      (by
        intro s hs
        exact hf1.differentiable (by norm_num) s)
      (by
        intro s hs
        exact
          (hU.differentiable (by norm_num) (x - s)).comp s
            ((differentiableAt_const (c := x)).sub differentiableAt_id))
  have hi' :
      ∫ s : E, (fderiv ℝ f s) v * g s ∂volume =
        ∫ s : E, f s * (fderiv ℝ U (x - s)) v ∂volume := by
    calc
      ∫ s : E, (fderiv ℝ f s) v * g s ∂volume =
          -∫ s : E, f s * (fderiv ℝ g s) v ∂volume := by
            linarith
      _ = ∫ s : E, f s * (fderiv ℝ U (x - s)) v ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [htrans]
        ring
  have hleft' :
      ∫ t : E, q t v ∂volume =
        ∫ t : E, (fderiv ℝ f t) v * g t ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with t
    change
      U (x - t) * (fderiv ℝ f t) v =
        (fderiv ℝ f t) v * U (x - t)
    ring
  have hright :
      ∫ t : E, inner ℝ v (f t • gradient U (x - t)) ∂volume =
        ∫ t : E, f t * (fderiv ℝ U (x - t)) v ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [real_inner_smul_right]
    rw [real_inner_comm]
    rw [inner_gradient_left]
  calc
    ∫ t : E, q t v ∂volume =
        ∫ t : E, (fderiv ℝ f t) v * g t ∂volume := hleft'
    _ = ∫ t : E, f t * (fderiv ℝ U (x - t)) v ∂volume := hi'
    _ = ∫ t : E, inner ℝ v (f t • gradient U (x - t)) ∂volume := hright.symm
    _ = ∫ t : E,
        inner ℝ v
          (((ContinuousLinearMap.lsmul ℝ ℝ)
            (φ.normed (volume : Measure E) t)) (gradient U (x - t))) ∂volume := by
      simp [f, ContinuousLinearMap.lsmul_apply]
