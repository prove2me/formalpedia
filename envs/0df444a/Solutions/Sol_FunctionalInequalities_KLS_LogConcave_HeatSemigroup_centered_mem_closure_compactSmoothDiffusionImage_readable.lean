-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.HeatSemigroup.centered_mem_closure_compactSmoothDiffusionImage_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:45.898506+00:00
-- url     : https://prove2.me/submissions/96ac62a8-e884-44d7-8bcb-42a9553c1ba0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_mem_closure_range_of_inner_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_eq_const_mean_of_closedWeightedOperator_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable

section
noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, `A y = 0` exactly when `T y = 0`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff (y : (adjointComp T).domain) :
    adjointComp T y = 0 ↔ T ⟨y, y.2.2⟩ = 0 := by
  constructor
  · intro hA
    have hnorm2 : ‖T ⟨(y : H₀), y.2.2⟩‖ ^ 2 = 0 := by
      rw [← inner_adjointComp_self hd y, hA, inner_zero_left]
    have hnorm : ‖T ⟨(y : H₀), y.2.2⟩‖ = 0 := by
      nlinarith [hnorm2]
    exact norm_eq_zero.mp hnorm
  · intro h
    refine hd.eq_zero_of_inner_left ℝ (fun z hz => ?_)
    rw [inner_adjointComp hd y hz, h, inner_zero_left]
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
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Every mean-zero real `L²` class is approximable by literal compact smooth diffusion images. -/
theorem solution
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : FunctionalInequalities.L2.mean ν g = 0) :
    g ∈ closure (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage hU) := by
  have hi : (interior (ν : Measure V).support).Nonempty :=
    FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_readable m hνU
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let A := FunctionalInequalities.Analysis.Semigroup.adjointComp T
  have hTc : T.IsClosed := by
    dsimp [T]
    exact hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  have hTd : Dense (T.domain : Set (Lp ℝ 2 (ν : Measure V))) := by
    dsimp [T]
    exact hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have horth : ∀ k : A.domain, A k = 0 →
      ⟪g, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
    intro k hk
    have hkT : T ⟨(k : Lp ℝ 2 (ν : Measure V)), k.2.2⟩ = 0 := by
      exact (FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff T hTd k).mp hk
    have hkconst : (k : Lp ℝ 2 (ν : Measure V)) =
        FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) := by
      simpa [T] using
        (FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero_readable m hν hi hνU hU.continuous
          ⟨(k : Lp ℝ 2 (ν : Measure V)), k.2.2⟩ (by simpa [T] using hkT))
    have hcs : FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) =
        (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) • FunctionalInequalities.L2.const ν 1 := by
      simpa using
        (FunctionalInequalities.L2.const_smul ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) 1)
    calc
      ⟪g, (k : Lp ℝ 2 (ν : Measure V))⟫ =
          ⟪g, FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ :=
        congrArg (fun z => ⟪g, z⟫) hkconst
      _ = (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) * FunctionalInequalities.L2.mean ν g := by
        rw [hcs]
        simpa only [FunctionalInequalities.L2.mean] using
          (real_inner_smul_right g (FunctionalInequalities.L2.const ν 1)
            (FunctionalInequalities.L2.mean ν (k : Lp ℝ 2 (ν : Measure V))))
      _ = 0 := by rw [hg, mul_zero]
  have hgRange : g ∈ closure (Set.range fun y : A.domain => A y) := by
    exact FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_readable T hTc hTd g horth
  have hsubset : closure (Set.range fun y : A.domain => A y) ⊆
      closure (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage hU) := by
    apply closure_minimal
    · rintro z ⟨y, rfl⟩
      obtain ⟨fn, hfn, hfnc, hF, hA⟩ :=
        hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU y
      let yn : ℕ → A.domain := fun n =>
        ⟨(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν
            (hfn n) (hfnc n)).toLp (fn n), by
          simpa [A, T] using
            hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩
      have hAnorm : Tendsto (fun n => ‖A (yn n) - A y‖) atTop (𝓝 0) := by
        simpa [yn, A, T] using hA
      have hAtendsto : Tendsto (fun n => A (yn n)) atTop (𝓝 (A y)) := by
        refine Metric.tendsto_atTop.2 ?_
        intro ε hε
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hAnorm) ε hε
        refine ⟨N, ?_⟩
        intro n hn
        simpa [dist_eq_norm] using hN n hn
      have hyn : ∀ n, A (yn n) ∈ FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage hU := by
        intro n
        refine ⟨fn n, hfn n, hfnc n, ?_⟩
        simpa [yn, A, T] using
          (hν.adjointComp_toLp_eq m hi hνU hU (hfn n) (hfnc n))
      exact mem_closure_of_tendsto hAtendsto
        (Filter.Eventually.of_forall hyn)
    · exact isClosed_closure
  exact hsubset hgRange
