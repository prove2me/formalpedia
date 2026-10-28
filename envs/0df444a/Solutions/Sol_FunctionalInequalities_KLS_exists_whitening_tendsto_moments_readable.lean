-- Prove2me | solution 1 for FunctionalInequalities.KLS.exists_whitening_tendsto_moments_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:53.591126+00:00
-- url     : https://prove2.me/submissions/e1874f97-762a-43f6-93ac-ec5a3da0fdff

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
import Theorems.Thm_FunctionalInequalities_KLS_covariance_tendsto_one_readable
import Theorems.Thm_FunctionalInequalities_KLS_whitening_sequence_readable

noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
section LT10BWhiteningMoments
open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
private lemma FunctionalInequalities.KLS.integrable_of_ball_support
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    {f : E → F} (hf : Continuous f) :
    Integrable f (ν : Measure E) := by
  have ha : ∀ᵐ x ∂(ν : Measure E), x ∈ closedBall (0 : E) R :=
    ae_iff.mpr hs
  have hi := hf.continuousOn.integrableOn_compact
    (μ := (ν : Measure E)) (isCompact_closedBall (0 : E) R)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section MeasurableSpace
variable [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.KLS.memLp_two_of_ball_support
    (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0) :
    MemLp id 2 (ν : Measure E) := by
  apply (memLp_two_iff_integrable_sq_norm
    continuous_id.aestronglyMeasurable).2
  exact integrable_of_ball_support ν hs (by fun_prop)
/-- Uniform convergence on the supporting ball gives a bound independent of the law. -/
private lemma FunctionalInequalities.KLS.affine_integral_perturbation
    {lam : ℕ → ProbabilityMeasure E} {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    {A : ℕ → E →L[ℝ] E} {c : ℕ → E}
    (hA : Tendsto A atTop (𝓝 1)) (hc : Tendsto c atTop (𝓝 0))
    {f : E → ℝ} (hf : Continuous f) :
    Tendsto
      (fun k => (∫ x, f (A k (x - c k)) ∂(lam k : Measure E)) -
        ∫ x, f x ∂(lam k : Measure E))
      atTop (𝓝 0) := by
  let : CompactSpace (closedBall (0 : E) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  let F : ((E →L[ℝ] E) × E) → closedBall (0 : E) R → ℝ :=
    fun p x => f (p.1 ((x : E) - p.2))
  have hF : Continuous ↿F := by
    dsimp only [F]
    exact hf.comp (by fun_prop)
  have hu := Continuous.tendstoUniformly F hF (1, 0)
  have hp := hA.prodMk_nhds hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hp.eventually
    ((Metric.tendstoUniformly_iff.mp hu) (ε / 2) (half_pos hε))
  filter_upwards [he] with k hk
  have hb : ∀ᵐ x ∂(lam k : Measure E),
      ‖f (A k (x - c k)) - f x‖ ≤ ε / 2 := by
    filter_upwards [show ∀ᵐ x ∂(lam k : Measure E),
        x ∈ closedBall (0 : E) R from ae_iff.mpr (hsupp k)] with x hx
    have hh := hk ⟨x, hx⟩
    have hh' : dist (f x) (f (A k (x - c k))) < ε / 2 := by
      simpa only [F, sub_zero, one_apply_eq_self] using hh
    rw [dist_comm, dist_eq_norm] at hh'
    exact hh'.le
  have hi : Integrable (fun x => f (A k (x - c k))) (lam k : Measure E) :=
    integrable_of_ball_support (lam k) (hsupp k) (hf.comp (by fun_prop))
  have hj : Integrable f (lam k : Measure E) :=
    integrable_of_ball_support (lam k) (hsupp k) hf
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hi hj, probReal_univ, mul_one] at hb'
  rw [dist_zero_right]
  exact hb'.trans_lt (half_lt_self hε)
private lemma FunctionalInequalities.KLS.mean_tendsto_zero
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    Tendsto (fun k => ∫ x, x ∂(lam k : Measure E)) atTop (𝓝 0) := by
  have hv (v : E) :
      Tendsto (fun k => ⟪v, ∫ x, x ∂(lam k : Measure E)⟫)
        atTop (𝓝 (0 : ℝ)) := by
    have h_lam (k : ℕ) :
        (∫ x, ⟪v, x⟫ ∂(lam k : Measure E)) =
          ⟪v, ∫ x, x ∂(lam k : Measure E)⟫ := by
      exact (innerSL ℝ v).integral_comp_comm
        (integrable_of_ball_support (lam k) (hsupp k) continuous_id)
    have h_mu : (∫ x, ⟪v, x⟫ ∂(μ : Measure E)) = 0 := by
      have hi : Integrable (fun x : E => x) (μ : Measure E) :=
        hiso.memLp_two.integrable (by norm_num)
      have hh := (innerSL ℝ v).integral_comp_comm hi
      change (∫ x, ⟪v, x⟫ ∂(μ : Measure E)) =
        ⟪v, ∫ x, x ∂(μ : Measure E)⟫ at hh
      rw [hh, hiso.mean_zero, inner_zero_right]
    simpa only [Fin.prod_univ_one, h_lam, h_mu] using
      hmom 1 (by norm_num) (fun _ => v)
  let b := stdOrthonormalBasis ℝ E
  have h := tendsto_finsetSum Finset.univ
    (fun i _ => (hv (b i)).smul_const (b i))
  simpa only [b.sum_repr', zero_smul, Finset.sum_const_zero] using h
private lemma FunctionalInequalities.KLS.covariance_positive
    (ν : ProbabilityMeasure E) :
    (Covariance.operator (ν : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).2
  constructor
  · intro x y
    change ⟪Covariance.operator (ν : Measure E) x, y⟫ =
      ⟪x, Covariance.operator (ν : Measure E) y⟫
    calc
      _ = ProbabilityTheory.covarianceBilin (ν : Measure E) x y :=
        Covariance.operator_inner _ _ _
      _ = ProbabilityTheory.covarianceBilin (ν : Measure E) y x :=
        ProbabilityTheory.covarianceBilin_comm x y
      _ = ⟪Covariance.operator (ν : Measure E) y, x⟫ :=
        (Covariance.operator_inner _ _ _).symm
      _ = _ := real_inner_comm _ _
  · intro x
    rw [Covariance.operator_inner]
    exact ProbabilityTheory.covarianceBilin_self_nonneg x
end MeasurableSpace
/-- **Whitening preserves convergence of low moments** (Letwin Lemma A.1 approximation): if the laws
`λ k`, all carried by a fixed ball, have mixed moments of degree `≤ 4` converging to those of an isotropic `μ`, then
there are affine maps `x ↦ L k (x − c k)` that make `λ k` isotropic for large `k` (mean zero, identity second
moments) and keep the convergence of the moments of degree `≤ 4`. -/
theorem solution [MeasurableSpace E] [BorelSpace E] {lam : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hiso : FunctionalInequalities.KLS.Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hμsupp : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    ∃ (L : ℕ → E ≃L[ℝ] E) (c : ℕ → E),
      (∀ᶠ k in atTop, ∫ x, L k (x - c k) ∂(lam k : Measure E) = 0 ∧
        ∀ u v : E, ∫ x, ⟪u, L k (x - c k)⟫ * ⟪v, L k (x - c k)⟫ ∂(lam k : Measure E) = ⟪u, v⟫) ∧
      ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
        Tendsto (fun k => ∫ x, ∏ i, ⟪v i, L k (x - c k)⟫ ∂(lam k : Measure E)) atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
  classical
  have hiso : FunctionalInequalities.KLS.Isotropic μ :=
    ⟨FunctionalInequalities.KLS.memLp_two_of_ball_support μ hμsupp, hiso.mean_zero, hiso.covariance_identity⟩
  let m : ℕ → E := fun k => ∫ x, x ∂(lam k : Measure E)
  let C : ℕ → E →L[ℝ] E := fun k => FunctionalInequalities.Covariance.operator (lam k : Measure E)
  have hm : Tendsto m atTop (𝓝 0) :=
    FunctionalInequalities.KLS.mean_tendsto_zero hiso hsupp hmom
  have hC : Tendsto C atTop (𝓝 1) :=
    FunctionalInequalities.KLS.covariance_tendsto_one_readable hiso hsupp hmom
  obtain ⟨L, hL, hwhite⟩ :=
    FunctionalInequalities.KLS.whitening_sequence_readable C (fun k => FunctionalInequalities.KLS.covariance_positive (lam k)) hC
  refine ⟨L, m, ?_, ?_⟩
  · filter_upwards [hwhite] with k hk
    let W := (L k).toContinuousLinearMap
    have hsa : IsSelfAdjoint W := hk.1
    have hsand : W * C k * W = 1 := hk.2
    have hi : Integrable (fun x : E => x) (lam k : Measure E) :=
      FunctionalInequalities.KLS.integrable_of_ball_support (lam k) (hsupp k) continuous_id
    have htwo := FunctionalInequalities.KLS.memLp_two_of_ball_support (lam k) (hsupp k)
    constructor
    · change (∫ x, W (x - m k) ∂(lam k : Measure E)) = 0
      have hsub : Integrable (fun x : E => x - m k) (lam k : Measure E) :=
        FunctionalInequalities.KLS.integrable_of_ball_support (lam k) (hsupp k) (by fun_prop)
      have hcomm :
          (∫ x, W (x - m k) ∂(lam k : Measure E)) =
            W (∫ x, x - m k ∂(lam k : Measure E)) :=
        W.integral_comp_comm hsub
      rw [hcomm, integral_sub hi (integrable_const (m k))]
      simp only [integral_const, probReal_univ, one_smul]
      change W (m k - m k) = 0
      rw [sub_self, map_zero]
    · intro u v
      change (∫ x, ⟪u, W (x - m k)⟫ * ⟪v, W (x - m k)⟫
        ∂(lam k : Measure E)) = ⟪u, v⟫
      calc
        _ = ProbabilityTheory.covarianceBilin (lam k : Measure E) (W u) (W v) := by
          simp_rw [← W.adjoint_inner_left, hsa.adjoint_eq]
          exact (ProbabilityTheory.covarianceBilin_apply htwo (W u) (W v)).symm
        _ = ⟪C k (W u), W v⟫ :=
          (FunctionalInequalities.Covariance.operator_inner (lam k : Measure E) (W u) (W v)).symm
        _ = ⟪W (C k (W u)), v⟫ := by
          rw [← W.adjoint_inner_right, hsa.adjoint_eq]
        _ = ⟪u, v⟫ := by
          have hh := congrArg (fun T : E →L[ℝ] E => T u) hsand
          change W (C k (W u)) = u at hh
          rw [hh]
  · intro d hd v
    have hp := FunctionalInequalities.KLS.affine_integral_perturbation hsupp hL hm
      (f := fun x => ∏ i, ⟪v i, x⟫) (by fun_prop)
    have hr := hmom d hd v
    simpa only [sub_add_cancel, zero_add, ContinuousLinearEquiv.coe_coe] using hp.add hr
