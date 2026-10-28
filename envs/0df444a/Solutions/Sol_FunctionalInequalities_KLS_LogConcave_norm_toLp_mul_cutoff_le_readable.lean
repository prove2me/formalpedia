-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_toLp_mul_cutoff_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:28.566255+00:00
-- url     : https://prove2.me/submissions/73b93cac-13be-4e1f-9f00-026fe075d68f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_weightedLaplacian_eq_zero_of_notMem_tsupport_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_mem_domain_closedWeightedOperator_toLp_mul_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_graph_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Product rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp
end Gradient
end DifferentialTools
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
open MeasureTheory Filter Topology
section
variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
section BddSmul
variable {c : α → ℝ} {M : ℝ}
theorem FunctionalInequalities.L2.coeFn_bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulL hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  coeFn_bddSmulₗ hc hM u
end BddSmul
section BddSmulRight
variable {β : α → H} {M : ℝ}
theorem FunctionalInequalities.L2.coeFn_bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightL hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  coeFn_bddSmulRightₗ hβ hM u
end BddSmulRight
section Symmetry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : α → ℝ} {M : ℝ}
/-- **A real a.e. bounded scalar multiplier is symmetric on `L²`.** Multiplication by `c` may be
moved from one side of the `L²` inner product to the other; this is the pointwise identity
`⟪c • a, b⟫ = ⟪a, c • b⟫` integrated. The multiplier is real valued, so no conjugation occurs. -/
theorem FunctionalInequalities.L2.inner_bddSmulL_left (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u v : Lp E 2 μ) :
    inner ℝ (bddSmulL hc hM u) v = inner ℝ u (bddSmulL hc hM v) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bddSmulL hc hM u, coeFn_bddSmulL hc hM v] with x h1 h2
  rw [h1, h2, real_inner_smul_left, real_inner_smul_right]
end Symmetry
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Multiplier
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- The domain clause of `exists_mem_domain_closedWeightedOperator_toLp_mul`. -/
theorem FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain) :
    (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain :=
  (hν.exists_mem_domain_closedWeightedOperator_toLp_mul_readable m B hi hφ hφc x).choose
/-- The value clause of `exists_mem_domain_closedWeightedOperator_toLp_mul`. -/
theorem FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_toLp_mul {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain)
    (hmem : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain) :
    ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
      =ᵐ[(ν : Measure V)] fun y =>
        φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
          + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y :=
  (hν.exists_mem_domain_closedWeightedOperator_toLp_mul_readable m B hi hφ hφc x).choose_spec
end Multiplier
end
end
end

noncomputable section
open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_nonneg (r : ℝ) (y : V) : 0 ≤ FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).nonneg
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_le_one (r : ℝ) (y : V) : FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y ≤ 1 :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).le_one
private theorem FunctionalInequalities.KLS.LogConcave.abs_cutoff_le_one (r : ℝ) (y : V) : |FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y| ≤ 1 :=
  abs_le.mpr ⟨le_trans (by norm_num) (cutoff_nonneg r y), cutoff_le_one r y⟩
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_eq_one {r : ℝ} (hr : 0 < r) {y : V} (hy : ‖y‖ ≤ 5 * r) :
    FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y = 1 := by
  apply (FunctionalInequalities.KLS.LogConcave.profile (V := V)).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← div_eq_inv_mul, div_le_iff₀ hr]
  exact hy
/-- On the open ball where the cutoff is constantly one its gradient vanishes. -/
private theorem FunctionalInequalities.KLS.LogConcave.gradient_cutoff_eq_zero {r : ℝ} (hr : 0 < r) {y : V} (hy : ‖y‖ < 5 * r) :
    gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y = 0 := by
  have hmem : y ∈ ball (0 : V) (5 * r) := by
    rw [mem_ball, dist_zero_right]; exact hy
  have hev : FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds hmem] with z hz
    rw [mem_ball, dist_zero_right] at hz
    exact cutoff_eq_one hr hz.le
  rw [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]
/-- The gradient vanishes outside the closed support. -/
private theorem FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    gradient f y = 0 := by
  have h : fderiv ℝ f y = 0 := by
    by_contra h
    exact hy (support_fderiv_subset (𝕜 := ℝ) h)
  rw [gradient, h, map_zero]
end Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Criterion
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
/-- The scaled-cutoff estimate behind the criterion: a class annihilating `(A + 1) C_c^∞(V)`
whose localizations all lie in `D(T̄)` has `‖χ_r u‖ ≤ (M / r) ‖u‖` for the cutoff family. -/
 theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
    (hM : ∀ y : V, ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ ≤ M / r) :
    ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff r)
        (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff hr) u).toLp _‖ ≤ (M / r) * ‖u‖ := by
  classical
  have hd : Dense ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain : Set
    (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hr2 : (0:ℝ) < 2 * r := by linarith
  have hr4 : (0:ℝ) < 4 * r := by linarith
  have hMr : 0 ≤ M / r := div_nonneg hM0 hr.le
  -- the three cutoffs
  have hχs : ContDiff ℝ ∞ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) := FunctionalInequalities.KLS.LogConcave.contDiff_cutoff r
  have hχc : HasCompactSupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) := FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff hr
  have hξs : ContDiff ℝ ∞ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r)) := FunctionalInequalities.KLS.LogConcave.contDiff_cutoff _
  have hξc : HasCompactSupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r)) := FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff hr2
  have hζs : ContDiff ℝ ∞ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r)) := FunctionalInequalities.KLS.LogConcave.contDiff_cutoff _
  have hζc : HasCompactSupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r)) := FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff hr4
  have hχm : AEStronglyMeasurable (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r)
    (ν : Measure V) := hχs.continuous.aestronglyMeasurable
  have hξm : AEStronglyMeasurable (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r)) (ν : Measure V) :=
    hξs.continuous.aestronglyMeasurable
  have hχb : ∀ᵐ y ∂(ν : Measure V), |FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y| ≤ 1 :=
    Filter.Eventually.of_forall (FunctionalInequalities.KLS.LogConcave.abs_cutoff_le_one r)
  have hξb : ∀ᵐ y ∂(ν : Measure V), |FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y| ≤ 1 :=
    Filter.Eventually.of_forall (FunctionalInequalities.KLS.LogConcave.abs_cutoff_le_one (2 * r))
  have hgχm : AEStronglyMeasurable (gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r)) (ν : Measure V) :=
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (hχs.of_le (mod_cast le_top))).aestronglyMeasurable
  have hgξm : AEStronglyMeasurable (gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r))) (ν : Measure V) :=
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (hξs.of_le (mod_cast le_top))).aestronglyMeasurable
  have hgχb : ∀ᵐ y ∂(ν : Measure V), ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ ≤ M / r :=
    Filter.Eventually.of_forall hM
  obtain ⟨Nξ, hNξ⟩ := (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (hξs.of_le (mod_cast le_top))
      (f := FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r))).bounded_above_of_compact_support
    (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hξc)
  have hgξb : ∀ᵐ y ∂(ν : Measure V), ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r)) y‖ ≤ Nξ :=
    Filter.Eventually.of_forall hNξ
  -- where the larger cutoffs are identically one
  have hnorm_le : ∀ y : V, y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) → ‖y‖ ≤ 8 * r := by
    intro y hy
    have := FunctionalInequalities.KLS.LogConcave.tsupport_cutoff_subset hr hy
    rwa [mem_closedBall, dist_zero_right] at this
  have hξone : ∀ y : V, y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) → FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y = 1 := by
    intro y hy
    exact FunctionalInequalities.KLS.LogConcave.cutoff_eq_one hr2 (le_trans (hnorm_le y hy) (by linarith))
  have hgξzero : ∀ y : V, y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) →
      gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r)) y = 0 := by
    intro y hy
    exact FunctionalInequalities.KLS.LogConcave.gradient_cutoff_eq_zero hr2 (lt_of_le_of_lt (hnorm_le y hy) (by linarith))
  have hζone : ∀ y : V, y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r)) →
      FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r) y = 1 := by
    intro y hy
    have := FunctionalInequalities.KLS.LogConcave.tsupport_cutoff_subset hr2 hy
    rw [mem_closedBall, dist_zero_right] at this
    exact FunctionalInequalities.KLS.LogConcave.cutoff_eq_one hr4 (le_trans this (by linarith))
  -- the three domain elements
  have hwmem : (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hζs hζc u).toLp _ ∈
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
    hloc _ hζs hζc
  have hw₁mem := hν.toLp_mul_mem_closedWeightedOperator_domain m (ContinuousLinearMap.id ℝ V) hi
    hχs hχc (⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
  have hzmem := hν.toLp_mul_mem_closedWeightedOperator_domain m (ContinuousLinearMap.id ℝ V) hi
    hχs hχc (⟨_, hw₁mem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
  have hζone2 : ∀ y : V, y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) → FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r) y = 1 := by
    intro y hy
    exact FunctionalInequalities.KLS.LogConcave.cutoff_eq_one hr4 (le_trans (hnorm_le y hy) (by linarith))
  -- representatives
  have hw_ae := (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hζs hζc u).coeFn_toLp
  have hw₁_ae := (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc
    (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
      (Lp ℝ 2 (ν : Measure V)))).coeFn_toLp
  have hz_ae := (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc
    (((⟨_, hw₁mem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
      (Lp ℝ 2 (ν : Measure V)))).coeFn_toLp
  have hcu_ae := (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).coeFn_toLp
  have hTw₁ := hν.coeFn_closedWeightedOperator_toLp_mul m (ContinuousLinearMap.id ℝ V) hi hχs hχc
    (⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) hw₁mem
  have hTz := hν.coeFn_closedWeightedOperator_toLp_mul m (ContinuousLinearMap.id ℝ V) hi hχs hχc
    (⟨_, hw₁mem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) hzmem
  -- the two auxiliary `L²` classes
  set p : (Lp V 2 (ν : Measure V)) := FunctionalInequalities.L2.bddSmulL (H := V) hχm hχb
    ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) with hp
  set q : (Lp V 2 (ν : Measure V)) := FunctionalInequalities.L2.bddSmulRightL (H := V) hgχm hgχb
    (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
      (Lp ℝ 2 (ν : Measure V))) with hq
  have hp_ae := FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hχm hχb
    ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))
  have hq_ae := FunctionalInequalities.L2.coeFn_bddSmulRightL (H := V) hgχm hgχb (((⟨_, hwmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
      (ν : Measure V)))
  -- `T̄ z = χ p + 2 χ q`
  have hA : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
      = FunctionalInequalities.L2.bddSmulL (H := V) hχm hχb p + (2 : ℝ) • FunctionalInequalities.L2.bddSmulL (H := V) hχm hχb q := by
    refine Lp.ext ?_
    filter_upwards [hTz, hTw₁, hw₁_ae, hp_ae, hq_ae,
      FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hχm hχb p, FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hχm hχb q,
      Lp.coeFn_add (FunctionalInequalities.L2.bddSmulL (H := V) hχm hχb p)
        ((2 : ℝ) • FunctionalInequalities.L2.bddSmulL (H := V) hχm hχb q),
      Lp.coeFn_smul (2 : ℝ) (FunctionalInequalities.L2.bddSmulL (H := V) hχm hχb q)] with
      y e1 e2 e3 e4 e5 e6 e7 e8 e9
    rw [e1, e8, Pi.add_apply, e6, e9, Pi.smul_apply, e7, e4, e5, e2, e3, FunctionalInequalities.Energy.WeightedGradient.apply_id]
    module
  -- `⟪T̄ z, T̄ w⟫ = ‖p‖² + 2 ⟪q, p⟫`
  have hB : ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫
      = ‖p‖ ^ 2 + 2 * ⟪q, p⟫ := by
    rw [hA, inner_add_left, real_inner_smul_left,
      FunctionalInequalities.L2.inner_bddSmulL_left (E := V) hχm hχb p
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)),
      FunctionalInequalities.L2.inner_bddSmulL_left (E := V) hχm hχb q
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)),
      ← hp, real_inner_self_eq_norm_sq]
  -- the tested class is `χ² u`
  have hζm : AEStronglyMeasurable (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r)) (ν : Measure V) :=
    hζs.continuous.aestronglyMeasurable
  have hζb : ∀ᵐ y ∂(ν : Measure V), |FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r) y| ≤ 1 :=
    Filter.Eventually.of_forall (FunctionalInequalities.KLS.LogConcave.abs_cutoff_le_one (4 * r))
  have hc_eq : (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _
      = FunctionalInequalities.L2.bddSmulL (H := ℝ) hχm hχb u := by
    refine Lp.ext ?_
    filter_upwards [hcu_ae, FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hχm hχb u] with y e1 e2
    rw [e1, e2, smul_eq_mul]
  have hw_eq : (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
    hi).domain)) : (Lp ℝ 2 (ν : Measure V))) = FunctionalInequalities.L2.bddSmulL (H := ℝ) hζm hζb u := by
    refine Lp.ext ?_
    filter_upwards [hw_ae, FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hζm hζb u] with y e1 e2
    rw [e1, e2, smul_eq_mul]
  have hz_eq : (((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
    hi).domain)) : (Lp ℝ 2 (ν : Measure V)))
      = FunctionalInequalities.L2.bddSmulL (H := ℝ) hχm hχb
        ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _) := by
    refine Lp.ext ?_
    filter_upwards [hz_ae, hw₁_ae, hw_ae, hcu_ae,
      FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hχm hχb
        ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _)] with y e1 e2 e3 e4 e5
    rw [e1, e5, e4, e2, e3, smul_eq_mul]
    by_cases hy : y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r)
    · rw [hζone2 y hy]; ring
    · rw [image_eq_zero_of_notMem_tsupport hy]; ring
  have hC : ⟪(((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
    hi).domain)) : (Lp ℝ 2 (ν : Measure V))), u⟫
      = ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _‖ ^ 2 := by
    rw [hz_eq, FunctionalInequalities.L2.inner_bddSmulL_left (E := ℝ) hχm hχb _ u, ← hc_eq, real_inner_self_eq_norm_sq]
  -- the orthogonality identity
  have hD : ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫
      = -⟪(((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
        (Lp ℝ 2 (ν : Measure V))), u⟫ := by
    obtain ⟨g, hg, hgc, hcv1, hcv2⟩ := hν.exists_seq_smooth_tendsto_graph_readable m
      (ContinuousLinearMap.id ℝ V) hi (⟨_, hzmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    have hfs : ∀ n, ContDiff ℝ ∞ fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y :=
      fun n => hξs.mul (hg n)
    have hfc : ∀ n, HasCompactSupport fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y :=
      fun n => hξc.mul_right
    -- the gradient class of a smooth compactly supported function, in the two shapes used
    have hbridge : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc' : HasCompactSupport f),
        (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf
            hfc').memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) f)
          = (FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport hf hfc').toLp (gradient f) := by
      intro f hf hfc'
      refine Lp.ext ?_
      filter_upwards [(FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf
          hfc').memLp_apply.coeFn_toLp,
        (FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport hf hfc').coeFn_toLp] with y e1 e2
      rw [e1, e2, FunctionalInequalities.Energy.WeightedGradient.apply_id]
    -- `[ξ gₙ] → z` in `L²`
    have hfL : ∀ n, (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).toLp _
        = FunctionalInequalities.L2.bddSmulL (H := ℝ) hξm hξb
          ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
      intro n
      refine Lp.ext ?_
      filter_upwards [(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).coeFn_toLp,
        FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hξm hξb
          ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
        (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp] with y e1 e2 e3
      rw [e1, e2, e3, smul_eq_mul]
    have hξz : FunctionalInequalities.L2.bddSmulL (H := ℝ) hξm hξb ((((⟨_, hzmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V))))
        = (((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V))) := by
      refine Lp.ext ?_
      filter_upwards [FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hξm hξb
        ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V)))), hz_ae] with y e1 e2
      rw [e1, e2, smul_eq_mul]
      by_cases hy : y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r)
      · rw [hξone y hy]; ring
      · rw [image_eq_zero_of_notMem_tsupport hy]; ring
    have hcvf : Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).toLp
        (fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y)) atTop
        (𝓝 ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
          hi).domain)) : (Lp ℝ 2 (ν : Measure V))))) := by
      have h := ((FunctionalInequalities.L2.bddSmulL (H := ℝ) hξm hξb).continuous.tendsto
        ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V))))).comp hcv1
      rw [hξz] at h
      exact h.congr fun n => (hfL n).symm
    -- `[∇(ξ gₙ)] → T̄ z` in `L²`
    have hgradf : ∀ n, (FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).toLp
          (gradient fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y)
        = FunctionalInequalities.L2.bddSmulL (H := V) hξm hξb
            ((FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).toLp (gradient (g n)))
          + FunctionalInequalities.L2.bddSmulRightL (H := V) hgξm hgξb
            ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
      intro n
      refine Lp.ext ?_
      filter_upwards [(FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).coeFn_toLp,
        Lp.coeFn_add (FunctionalInequalities.L2.bddSmulL (H := V) hξm hξb
            ((FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).toLp (gradient (g n))))
          (FunctionalInequalities.L2.bddSmulRightL (H := V) hgξm hgξb
            ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))),
        FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hξm hξb
          ((FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).toLp (gradient (g n))),
        FunctionalInequalities.L2.coeFn_bddSmulRightL (H := V) hgξm hgξb
          ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
        (FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).coeFn_toLp,
        (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp] with
        y e1 e2 e3 e4 e5 e6
      rw [e1, e2, Pi.add_apply, e3, e4, e5, e6,
        FunctionalInequalities.Analysis.BakryEmery.gradient_mul (hξs.differentiable (by simp)).differentiableAt
          ((hg n).differentiable (by simp)).differentiableAt]
    have hξTz : FunctionalInequalities.L2.bddSmulL (H := V) hξm hξb
      ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))
        = (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) := by
      refine Lp.ext ?_
      filter_upwards [FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hξm hξb
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)), hTz] with y e1 e2
      rw [e1, e2]
      by_cases hy : y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r)
      · rw [hξone y hy, one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hy, FunctionalInequalities.Energy.WeightedGradient.apply_id,
          FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport hy]
        simp
    have hgξ0 : FunctionalInequalities.L2.bddSmulRightL (H := V) hgξm hgξb ((((⟨_, hzmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V)))) = 0 := by
      refine Lp.ext ?_
      filter_upwards [FunctionalInequalities.L2.coeFn_bddSmulRightL (H := V) hgξm hgξb
          ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
            hi).domain)) : (Lp ℝ 2 (ν : Measure V)))), hz_ae,
        Lp.coeFn_zero (E := V) (p := 2) (μ := (ν : Measure V))] with y e1 e2 e3
      rw [e1, e3, Pi.zero_apply, e2]
      by_cases hy : y ∈ tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r)
      · rw [hgξzero y hy, smul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hy]; simp
    have hcvg : Tendsto (fun n => (FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hfs n)
        (hfc n)).toLp (gradient fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y)) atTop
        (𝓝 ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))) := by
      have hcv2' : Tendsto (fun n => (FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hg n)
          (hgc n)).toLp (gradient (g n))) atTop (𝓝
            ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))) :=
        hcv2.congr fun n => hbridge _ (hg n) (hgc n)
      have h := (((FunctionalInequalities.L2.bddSmulL (H := V) hξm hξb).continuous.tendsto
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))).comp hcv2').add
        (((FunctionalInequalities.L2.bddSmulRightL (H := V) hgξm hgξb).continuous.tendsto
          ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
            hi).domain)) : (Lp ℝ 2 (ν : Measure V))))).comp hcv1)
      rw [hξTz, hgξ0, add_zero] at h
      exact h.congr fun n => (hgradf n).symm
    -- the generator image of the localized test function, and where it lives
    have hAae : ∀ n, (((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))) : V → ℝ)
        =ᵐ[(ν : Measure V)] fun y => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U
          (fun z => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) z * g n z) y := by
      intro n
      rw [hν.adjointComp_toLp_eq m hi hνU hU (hfs n) (hfc n)]
      exact (FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := ν) hU (hfs n) (hfc n)).coeFn_toLp
    have hζ16 : ∀ (n : ℕ) (y : V),
        y ∈ tsupport (fun z => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) z * g n z) →
        FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (4 * r) y = 1 := fun n y hy => hζone y (tsupport_mul_subset_left hy)
    have hpair : ∀ n, ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫
        = ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n) (hfc n)⟩ : (Lp ℝ 2
            (ν : Measure V))),
            (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
              hi).domain)) : (Lp ℝ 2 (ν : Measure V)))⟫ := by
      intro n
      have h0 : ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))), u - (((⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
              (ν : Measure V)))⟫ = 0 := by
        rw [L2.inner_def]
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hAae n, Lp.coeFn_sub u (((⟨_, hwmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
            (ν : Measure V))),
          hw_ae] with y e1 e2 e3
        rw [Pi.zero_apply, Real.inner_apply, e1, e2, Pi.sub_apply, e3]
        by_cases hy : y ∈ tsupport (fun z => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) z * g n z)
        · rw [hζ16 n y hy]; ring
        · rw [FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_readable U hy]; ring
      rw [inner_sub_right, sub_eq_zero] at h0
      exact h0
    have hIBP : ∀ n, ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))), (((⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
              (ν : Measure V)))⟫
        = ⟪(FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).toLp
            (gradient fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫ := by
      intro n
      rw [FunctionalInequalities.Analysis.Semigroup.inner_adjointComp hd (⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
        (hfc n)⟩ : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) hwmem]
      congr 1
      exact hν.closedWeightedOperator_toLp_eq m hi (hfs n) (hfc n)
    have hkey : ∀ n, ⟪(FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).toLp
          (gradient fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫
        = -⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).toLp
            (fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y) : (Lp ℝ 2 (ν : Measure V))), u⟫ := by
      intro n
      have h := horth _ (hfs n) (hfc n)
      rw [← hIBP n, ← hpair n]
      linarith [h]
    have hlim1 : Tendsto (fun n => ⟪(FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (hfs n)
          (hfc n)).toLp (gradient fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫) atTop
        (𝓝 (⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫)) :=
      hcvg.inner tendsto_const_nhds
    have hlim2 : Tendsto (fun n => -⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfs n)
          (hfc n)).toLp (fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) (2 * r) y * g n y) : (Lp ℝ 2
            (ν : Measure V))), u⟫) atTop
        (𝓝 (-⟪(((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
          hi).domain)) : (Lp ℝ 2 (ν : Measure V))), u⟫)) :=
      (hcvf.inner tendsto_const_nhds).neg
    exact tendsto_nhds_unique (hlim1.congr hkey) hlim2
  -- the resulting quadratic estimate
  have hqnorm : ‖q‖ ≤ M / r * ‖u‖ := by
    have h1 : ‖q‖ ≤ |M / r| * ‖(((⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V)))‖ := by
      rw [hq]
      simpa using FunctionalInequalities.L2.norm_bddSmulRightₗ_le (H := V) hgχm hgχb
        (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V)))
    have h2 : ‖(((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
      hi).domain)) : (Lp ℝ 2 (ν : Measure V)))‖ ≤ ‖u‖ := by
      rw [hw_eq]
      simpa using FunctionalInequalities.L2.norm_bddSmulₗ_le (H := ℝ) hζm hζb u
    calc ‖q‖ ≤ |M / r| * ‖(((⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V)))‖ := h1
      _ = M / r * ‖(((⟨_, hwmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
          (ν : Measure V)))‖ := by rw [abs_of_nonneg hMr]
      _ ≤ M / r * ‖u‖ := by exact mul_le_mul_of_nonneg_left h2 hMr
  have hsq : ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _‖ ^ 2
      ≤ ‖q‖ ^ 2 := by
    have hcs : |⟪q, p⟫| ≤ ‖q‖ * ‖p‖ := abs_real_inner_le_norm q p
    have hid := hB.symm.trans (hD.trans (by rw [hC]))
    nlinarith [abs_nonneg (⟪q, p⟫ : ℝ), le_abs_self (⟪q, p⟫ : ℝ), neg_abs_le (⟪q, p⟫ : ℝ),
      norm_nonneg p, norm_nonneg q, sq_nonneg (‖p‖ - ‖q‖)]
  have hfinal : ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _‖ ≤ ‖q‖ := by
    nlinarith [norm_nonneg ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp
      (fun y => FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y * u y)), norm_nonneg q]
  exact hfinal.trans hqnorm
