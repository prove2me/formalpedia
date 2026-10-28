-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:47.079418+00:00
-- url     : https://prove2.me/submissions/d0e819e2-2a77-4fb2-87a8-e29b48d9a38d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Tilt
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_expTilt_of_memLp_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_neg_weightedLaplacian_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_tendsto_apply_of_tendsto_adjointComp_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
end CompleteSpace
end NormedSpace
/-- The tilt average of a class `g ∈ L²(μ)` at `z` is `(∫ e^{⟪z, x⟫} dμ)⁻¹ ⟪e^{⟪z, ·⟫}, g⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_Lp_eq_inner (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (g : Lp ℝ 2 μ) (z : E) :
    tiltAverage μ (⇑g) z =
      (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ * ⟪(memLp_exp_inner μ hexp z).toLp _, g⟫ := by
  rw [tiltAverage, expTilt, integral_tilted, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(memLp_exp_inner μ hexp z).coeFn_toLp] with x hx
  rw [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial, div_eq_mul_inv]
  ring
/-- For fixed `z`, `g ↦ F_g(z)` is continuous on `L²(μ)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.continuous_tiltAverage_Lp (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Continuous fun g : Lp ℝ 2 μ => tiltAverage μ (⇑g) z := by
  simp_rw [tiltAverage_Lp_eq_inner μ hexp _ z]
  exact continuous_const.mul (continuous_const.inner continuous_id)
end ScalarLp
omit [FiniteDimensional ℝ E] in
/-- Pairing the tilt average of a vector class `G ∈ L²(μ; E)` with `w` is the tilt average of the
scalar class `⟪w, G⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) (w z : E) :
    ⟪w, tiltAverage μ (⇑G) z⟫ = tiltAverage μ (⇑((innerSL ℝ w).compLpL 2 μ G)) z := by
  rw [tiltAverage_congr_ae μ ((innerSL ℝ w).coeFn_compLpL G) z]
  unfold tiltAverage
  simp only [innerSL_apply_apply]
  exact (integral_inner (integrable_expTilt_of_memLp_readable μ hexp (Lp.memLp G) z) w).symm
end Lp
end
end
end

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

section
noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Tilted
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
variable (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- **`C_c^∞(V)` is an operator core of the generator `A = T̄†T̄`.** For `ν = m.tilted (-U)` with
a `C¹` potential and unit weight, every `F ∈ D(A)` is the limit of smooth compactly supported
classes in the graph norm of `A`: there are `fₙ ∈ C_c^∞(V)` with `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. Equivalently, `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint on `C_c^∞(V)` in `L²(ν)`.

This is the operator-core criterion `exists_seq_smooth_tendsto_adjointComp_of_localRegularity`
with its hypothesis discharged by `toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`; it
is exactly the hypothesis `hcore` of `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.
No convexity of `U`, no semigroup and no `Γ₂` input is used. -/
theorem FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable m hi hνU hU
    (fun u horth _χ hχ hχc =>
      hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable m hi hνU hU u horth hχ hχc) F
end Tilted
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff RealInnerProductSpace ENNReal
section Generator
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
/-- (48) for smooth compactly supported classes, read on the `L²` classes `A [f] = [-ℒf]` and
`T̄ [f] = [∇f]`. -/
private theorem FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_toLp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (z : V) :
    tiltAverage (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩)) z =
      ⟪z, tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)) z⟫ := by
  rw [hν.adjointComp_toLp_eq m hi hνU hU hf hfc, hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    tiltAverage_congr_ae _ (MemLp.coeFn_toLp _) z,
    tiltAverage_congr_ae _ (MemLp.coeFn_toLp _) z, hνU]
  exact tiltAverage_neg_weightedLaplacian_readable m hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc z
/-- **BKL (48) on the generator domain**: for `ν = m.tilted (-U)` with `U ∈ C¹` and all
exponential moments, and `F ∈ D(A)`, `F_{A F}(z) = ⟪z, F_{T̄ F}(z)⟫` for every `z`. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (z : V) :
    FunctionalInequalities.Analysis.BakryEmery.tiltAverage (ν : Measure V)
        (⇑(FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
      ⟪z, FunctionalInequalities.Analysis.BakryEmery.tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫ := by
  obtain ⟨fn, hfn, hfnc, h0, h1⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU F
  let x : ℕ → (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :=
    fun n => ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩
  have hx0 : Tendsto (fun n => (x n : Lp ℝ 2 (ν : Measure V))) atTop
      (𝓝 (F : Lp ℝ 2 (ν : Measure V))) := tendsto_iff_norm_sub_tendsto_zero.2 h0
  have hx1 : Tendsto
      (fun n => FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (x n))
      atTop (𝓝 (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 h1
  have hT := FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_readable
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hx0 hx1
  have hL := ((FunctionalInequalities.Analysis.BakryEmery.continuous_tiltAverage_Lp (ν : Measure V) hexp z).tendsto _).comp hx1
  have hR := (((FunctionalInequalities.Analysis.BakryEmery.continuous_tiltAverage_Lp (ν : Measure V) hexp z).comp
    ((innerSL ℝ z).compLpL 2 (ν : Measure V)).continuous).tendsto _).comp hT
  rw [FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (ν : Measure V) hexp]
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  simp only [Function.comp_apply]
  rw [← FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (ν : Measure V) hexp]
  exact (FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_toLp_eq m hν hi hνU hU (hfn n) (hfnc n) z).symm
