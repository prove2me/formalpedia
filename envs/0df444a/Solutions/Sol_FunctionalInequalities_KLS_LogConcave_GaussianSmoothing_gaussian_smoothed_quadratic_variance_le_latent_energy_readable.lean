-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_smoothed_quadratic_variance_le_latent_energy_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:27:22.453979+00:00
-- url     : https://prove2.me/submissions/3017468a-f3e8-4dd6-b4ec-83a0aee64ad8

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_compact_dual_bound_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_of_continuousLinearEquiv_map_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_variance_le_sum_of_partial_dual_bounds_readable
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_mapContinuousLinearEquiv_readable
import Theorems.Thm_FunctionalInequalities_Probability_memLp_quadratic_of_memLp_four_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : MeasureTheory.ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁] in
/-- A full affine support stays full under a continuous linear equivalence. -/
theorem FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_eq_top (h : affineSupport ν = ⊤) :
    affineSupport (mapContinuousLinearEquiv ν T) = ⊤ := by
  rw [affineSupport_mapContinuousLinearEquiv_readable, h]
  exact AffineMap.map_top_of_surjective _ T.surjective
end ContinuousLinearEquiv
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
section Euclidean
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
section
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [CompleteSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The image of a log-concave law under a continuous linear equivalence is log-concave. -/
theorem FunctionalInequalities.KLS.LogConcave.mapContinuousLinearEquiv {ν : ProbabilityMeasure V₁} (hν : LogConcave ν) (T : V₁ ≃L[ℝ] V₂) :
    LogConcave (Probability.mapContinuousLinearEquiv ν T) :=
  hν.of_continuousLinearEquiv_map_readable _ T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).map_eq
end
section
omit [CompleteSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] in
/-- A log-concave law with full affine support has support with nonempty interior. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_affineSupport_eq_top {ν : ProbabilityMeasure V₁}
    (hν : LogConcave ν) (h : affineSupport ν = ⊤) :
    (interior (ν : Measure V₁).support).Nonempty :=
  hν.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr h
end
end Euclidean
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw_logConcave {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    {s : ℝ} (hs : 0 < s) :
    LogConcave (smoothedProbabilityLaw ν s hs) :=
  IsBorellDensity.compactLogConcave (ν := smoothedProbabilityLaw ν s hs)
    (normalizedDensity_isBorellDensity hρ hs)
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.lintegral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : V, ENNReal.ofReal (normalizedDensity ρ s x) = 1 := by
  have hprob := smoothedLaw_probability (ν := ν) hs
  rw [isProbabilityMeasure_iff] at hprob
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs,
    withDensity_apply _ MeasurableSet.univ] at hprob
  simpa only [Measure.restrict_univ] using hprob
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedDensity ρ s x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable]
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
/-- The normalized Gaussian convolution is exactly the tilted law of its
continuous convex logarithmic potential. Higher smoothness of the potential is a
separate analytic obligation. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_eq_tilted_potential {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    smoothedLaw ν s = (volume : Measure V).tilted (-(potential ρ s)) := by
  have hExp (x : V) : Real.exp (-potential ρ s x) =
      normalizedDensity ρ s x := by
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs x)]
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs]
  unfold Measure.tilted
  simp only [Pi.neg_apply]
  simp_rw [hExp]
  rw [integral_normalizedDensity_eq_one hρ hs]
  simp
end
end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal
section
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_four {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : ℝ} (hs : 0 < s) : MemLp id 4 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun x : E => Real.exp ((1 : ℝ) * ‖x‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  have hp := Probability.integrable_norm_pow_of_integrable_exp_norm
    (by norm_num : (0 : ℝ) < 1) he 4
  apply (integrable_norm_rpow_iff (f := (id : E → E)) continuous_id.aestronglyMeasurable
    (by norm_num : (4 : ENNReal) ≠ 0) (by simp : (4 : ENNReal) ≠ ∞)).mp
  simpa using hp
end
end
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_four (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ4 : MemLp id 4 μ) {s : ℝ} (hs : 0 < s) : MemLp id 4 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  unfold smoothedLaw Measure.conv
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact (hμ4.comp_fst (gaussianLaw s)).add ((gaussianLaw_memLp_four hs).comp_snd μ)
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.map_linear_memLp_four (μ : Measure E) (S : E →L[ℝ] E)
    (hμ4 : MemLp id 4 μ) : MemLp id 4 (μ.map S) := by
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable S.continuous.measurable.aemeasurable).2
  exact S.comp_memLp' hμ4
end
end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_convex_smooth_potential_smoothed_linearEquiv
    (μ : ProbabilityMeasure E) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (htop : Probability.affineSupport μ = ⊤) (S : E ≃L[ℝ] E)
    {s : ℝ} (hs : 0 < s) :
    ∃ W : E → ℝ, ContDiff ℝ ∞ W ∧ ConvexOn ℝ univ W ∧
      smoothedLaw ((μ : Measure E).map S) s = (volume : Measure E).tilted (-W) ∧
      FunctionalInequalities.KLS.LogConcave
        (smoothedProbabilityLaw (Probability.mapContinuousLinearEquiv μ S) s hs) := by
  let η := Probability.mapContinuousLinearEquiv μ S
  have hη : FunctionalInequalities.KLS.LogConcave η := hLC.mapContinuousLinearEquiv S
  have hηtop : Probability.affineSupport η = ⊤ :=
    Probability.affineSupport_mapContinuousLinearEquiv_eq_top μ S htop
  have hi := hη.interior_support_nonempty_of_affineSupport_eq_top hηtop
  obtain ⟨ρ,hρ⟩ := hη.exists_isBorellDensity_of_interior_support_nonempty volume hi
    (hη.absolutelyContinuous_of_interior_support_nonempty volume hi)
  exact ⟨potential ρ s, potential_contDiff_infty hρ hs, potential_convex hρ hs,
    smoothedLaw_eq_tilted_potential hρ hs, smoothedProbabilityLaw_logConcave hρ hs⟩
end
end
end

noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (hfull : FunctionalInequalities.Probability.affineSupport μ = ⊤)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hsource : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map
      (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : IsSelfAdjoint Q) {s : ℝ} (hs : 0 < s) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    variance (fun x => ⟪Q x,x⟫) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ((μ : Measure _).map S) s) ≤
      4 * ∑ i : Fin n, ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.toContinuousLinearMap.adjoint
          (Q (EuclideanSpace.single i 1)))) + (2*s)⁻¹ • Q (EuclideanSpace.single i 1)‖ ^ 2 ∂P := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E := volume.tilted (-u)
  let P := ρ.prod (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s)
  let ν := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw (FunctionalInequalities.Probability.mapContinuousLinearEquiv μ S) s hs
  let f : E → ℝ := fun x => ⟪Q x,x⟫
  let J : Fin n → ℝ := fun i => ∫ p : E × E,
    ‖S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.toContinuousLinearMap.adjoint
      (Q (EuclideanSpace.single i 1)))) + (2*s)⁻¹ • Q (EuclideanSpace.single i 1)‖ ^ 2 ∂P
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hexp
  have hgnorm (x : E) : ‖gradient u x‖ ≤ (L : ℝ) := by
    calc
      _ = ‖fderiv ℝ u x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ hL
  have hu4 : MemLp (gradient u) 4 ρ := MemLp.of_bound
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu).aestronglyMeasurable (L : ℝ) (ae_of_all _ hgnorm)
  have hμ4 : MemLp id 4 (μ : Measure E) := by
    rw [← hsource]
    exact (memLp_map_measure_iff continuous_id.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu).measurable.aemeasurable).2 hu4
  let : IsProbabilityMeasure ((μ : Measure E).map S.toContinuousLinearMap) :=
    (μ : Measure E).isProbabilityMeasure_map S.toContinuousLinearMap.continuous.measurable.aemeasurable
  have hν4 : MemLp id 4 (ν : Measure E) :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_four _ (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.map_linear_memLp_four _ S.toContinuousLinearMap hμ4) hs
  have hν2 : MemLp id 2 (ν : Measure E) := hν4.mono_exponent (by norm_num)
  obtain ⟨W,hW,hWc,hνW,hνLC⟩ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_convex_smooth_potential_smoothed_linearEquiv μ hLC hfull S hs
  have hf : ContDiff ℝ 1 f := Q.contDiff.inner ℝ contDiff_id
  have hf2 : MemLp f 2 (ν : Measure E) := FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_readable hν4 Q
  have hdf (x w : E) : fderiv ℝ f x w = 2 * ⟪x,Q w⟫ := by
    have hd := Q.hasFDerivAt.inner ℝ (hasFDerivAt_id (𝕜 := ℝ) x)
    change HasFDerivAt f _ x at hd
    rw [hd.fderiv]
    change ⟪Q x,w⟫ + ⟪Q w,x⟫ = 2 * ⟪x,Q w⟫
    have hqxw : ⟪Q x,w⟫ = ⟪x,Q w⟫ := hQ.isSymmetric x w
    rw [hqxw,real_inner_comm x (Q w)]
    ring
  have hdf2 (i : Fin n) : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (ν : Measure E) := by
    apply MemLp.ae_eq (ae_of_all _ fun x => (hdf x _).symm)
    exact (hν2.inner_const (𝕜 := ℝ) (Q (EuclideanSpace.single i 1))).const_mul 2
  have hK (i : Fin n) (h : E → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
      (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure E)) ^ 2 ≤
        (4 * J i) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure E) := by
    have hd := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_compact_dual_bound_readable μ ν hu hL hG hnorm hsource
      S.toContinuousLinearMap (Q (EuclideanSpace.single i 1)) hs rfl h hh hhc
    have hp : (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure E)) =
        2 * ∫ x, ⟪x,Q (EuclideanSpace.single i 1)⟫ * h x ∂(ν : Measure E) := by
      simp_rw [hdf]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    rw [hp]
    calc
      _ = 4 * (∫ x, ⟪x,Q (EuclideanSpace.single i 1)⟫ * h x ∂(ν : Measure E)) ^ 2 := by ring
      _ ≤ 4 * (J i * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure E)) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = _ := by ring
  have hv := FunctionalInequalities.KLS.LogConcave.variance_le_sum_of_partial_dual_bounds_readable volume hνLC hνW
    (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hWc hf hf2 hdf2 (fun i => 4 * J i) hK
  change variance f (ν : Measure E) ≤ 4 * ∑ i, J i
  simpa only [Finset.mul_sum] using hv
