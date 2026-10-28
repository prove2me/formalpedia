-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_tiltedDensity_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:49.641029+00:00
-- url     : https://prove2.me/submissions/097af892-558e-4680-b474-01666fbb2985

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff LinearPMap RealInnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Generator
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
include hνU hU in
/-- **the smooth-test generator identity, value clause**: for `f ∈ C_c^∞(V)`, `T̄†T̄ [f] = [-ℒ f]` with `ℒ f = Δ f - ⟪∇U, ∇f⟫`.
The generator of the heat semigroup `P_t = exp (-t T̄†T̄)` is therefore `ℒ` on smooth compactly
supported tests: `d/dt P_t f |_{t=0} = ℒ f`. -/
theorem FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨(memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f,
          hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ =
      (memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun x => -weightedLaplacian U f x) := by
  rw [adjointComp_apply]
  refine LinearPMap.adjoint_apply_eq
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) _ fun x => ?_
  rw [hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x]
  congr 1
  exact (hν.closedWeightedOperator_toLp_eq m hi hf hfc).symm
end Generator
end
end
end

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Density
variable {V : Type*} [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) {U : V → ℝ}
/-- `exp (-U)` is `m`-integrable when `m.tilted (-U)` is a probability measure. -/
private theorem FunctionalInequalities.KLS.LogConcave.integrable_exp_neg (hνU : (ν : Measure V) = m.tilted (-U)) :
    Integrable (fun x => Real.exp ((-U) x)) m := by
  by_contra h
  have h0 : (ν : Measure V) = 0 := by rw [hνU]; exact tilted_of_not_integrable h
  have h1 := measure_univ (μ := (ν : Measure V))
  rw [h0] at h1
  simp at h1
private theorem FunctionalInequalities.KLS.LogConcave.integral_eq_tiltedDensity (hνU : (ν : Measure V) = m.tilted (-U)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V → E) :
    ∫ x, g x ∂(ν : Measure V) = ∫ x, FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x • g x ∂m := by
  rw [hνU]
  exact integral_tilted _ _
end Density
section DensityIntegrable
variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) {U : V → ℝ}
/-- A bounded continuous compactly supported multiple of `ρ u` is `m`-integrable. -/
private theorem FunctionalInequalities.KLS.LogConcave.integrable_mul_tiltedDensity_mul (hνU : (ν : Measure V) = m.tilted (-U))
    (u : Lp ℝ 2 (ν : Measure V)) {h : V → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable (fun x => h x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x)) m := by
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  have hu : Integrable (fun x => h x * u x) (ν : Measure V) :=
    ((Lp.memLp u).integrable one_le_two).bdd_mul hh.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have key : ∀ μ : Measure V, μ = m.tilted (-U) → Integrable (fun x => h x * u x) μ →
      Integrable (fun x => Real.exp ((-U) x) • (h x * u x)) m := by
    rintro μ rfl hμ
    exact (integrable_tilted_iff (integrable_exp_neg m hνU) _).mp hμ
  have h1 := (key _ hνU hu).const_mul (∫ y, Real.exp ((-U) y) ∂m)⁻¹
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [FunctionalInequalities.KLS.LogConcave.tiltedDensity, smul_eq_mul, div_eq_mul_inv]
  ring
end DensityIntegrable
section Tilted
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
variable (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- **The weak equation for the density-weighted class `W = ρ u`.** If `u ∈ L²(ν)` is orthogonal
to `(A + 1) C_c^∞(V)`, then for every smooth compactly supported `f`,
`∫ Δf W dm = ∫ ⟪∇f, W ∇U⟫ dm + ∫ f W dm`: the equation `ℒ u = u` in `L²(ν)` is, against the
Haar measure, the divergence-form equation `Δ W = -div (W ∇U) + W` in the weak sense. -/
 theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ x, Laplacian.laplacian f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m =
      ∫ x, ⟪gradient f x, (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) • gradient U x⟫ ∂m +
        ∫ x, f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have h0 := horth f hf hfc
  rw [hν.adjointComp_toLp_eq m hi hνU hU hf hfc, L2.inner_def, L2.inner_def] at h0
  have h1 : ∫ x, ⟪((FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp
      (fun y => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f y) : Lp ℝ 2 (ν : Measure V)) x, u x⟫ ∂(ν : Measure V) =
      ∫ x, -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x * u x ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).coeFn_toLp] with x e
    rw [e, Real.inner_apply]
  have h2 : ∫ x, ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
      Lp ℝ 2 (ν : Measure V)) x, u x⟫ ∂(ν : Measure V) =
      ∫ x, f x * u x ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).coeFn_toLp] with x e
    rw [e, Real.inner_apply]
  rw [h1, h2, FunctionalInequalities.KLS.LogConcave.integral_eq_tiltedDensity m hνU (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x * u x),
    FunctionalInequalities.KLS.LogConcave.integral_eq_tiltedDensity m hνU (fun x => f x * u x)] at h0
  have hI1 := FunctionalInequalities.KLS.LogConcave.integrable_mul_tiltedDensity_mul m hνU u (FunctionalInequalities.Analysis.BakryEmery.continuous_laplacian hf2)
    (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_laplacian hfc)
  have hcont : Continuous fun x => ⟪gradient U x, gradient f x⟫ :=
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hU).inner (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hf1)
  have hcs : HasCompactSupport fun x => ⟪gradient U x, gradient f x⟫ := by
    refine HasCompactSupport.of_support_subset_isCompact (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hfc)
      fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by rw [hz, inner_zero_right])
  have hI2 := FunctionalInequalities.KLS.LogConcave.integrable_mul_tiltedDensity_mul m hνU u hcont hcs
  have hI1' : Integrable (fun x => -(Laplacian.laplacian f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x))) m :=
    hI1.neg
  have hsplit : ∫ x, FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x • (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x * u x) ∂m =
      -∫ x, Laplacian.laplacian f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m +
        ∫ x, ⟪gradient U x, gradient f x⟫ * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m := by
    rw [← integral_neg, ← integral_add hI1' hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_apply, smul_eq_mul]
    ring
  have hlast : ∫ x, FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x • (f x * u x) ∂m =
      ∫ x, f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring)
  rw [hsplit, hlast] at h0
  have hg : ∫ x, ⟪gradient f x, (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) • gradient U x⟫ ∂m =
      ∫ x, ⟪gradient U x, gradient f x⟫ * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      beta_reduce
      rw [real_inner_smul_right, real_inner_comm]; ring)
  rw [hg]
  linarith
