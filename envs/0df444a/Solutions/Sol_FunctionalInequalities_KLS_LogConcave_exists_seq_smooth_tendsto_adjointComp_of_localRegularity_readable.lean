-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:31.92564+00:00
-- url     : https://prove2.me/submissions/3ec2198a-9e0c-4a8d-bba3-16c215527931

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_eq_zero_of_localRegularity_readable

noncomputable section
open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Criterion
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
/-- **Operator-core criterion: local regularity of deficiency elements implies that `C_c^∞(V)`
is an operator core of `A = T̄†T̄`.**

Assume that every `u ∈ L²(ν)` orthogonal to `(A + 1) C_c^∞(V)` has all of its localizations
`[χ u]`, `χ ∈ C_c^∞(V)`, in the form domain `D(T̄)`. Then every `F ∈ D(A)` is the limit of smooth
compactly supported classes **in the graph norm of `A`**: `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. This is the hypothesis `hcore` of
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.

The proof is the standard deficiency argument: `eq_zero_of_localRegularity` says that the
orthogonal complement of the range of `A + 1` on `C_c^∞(V)` is trivial, so that range is dense;
and `‖(A + 1) v‖² = ‖A v‖² + 2 ‖T̄ v‖² + ‖v‖²` converts approximation of `(A + 1) F` into
simultaneous approximation of `F` and `A F`. Nothing beyond the stated hypothesis is assumed: the
potential is only `C¹` and no convexity, no semigroup and no `Γ₂` input is used. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (hreg : ∀ u : (Lp ℝ 2 (ν : Measure V)),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
          ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
            (ν : Measure V))), u⟫ = 0) →
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) := by
  classical
  have hd : Dense (((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain : Set
    (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  set Ψ : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain →ₗ[ℝ] (Lp ℝ 2
      (ν : Measure V)) := ((FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).toFun + ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain.subtype with hΨ
  have hΨapply : ∀ v : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain, Ψ v = ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) v : (Lp ℝ 2
        (ν : Measure V))) + (v : (Lp ℝ 2 (ν : Measure V))) := fun v => rfl
  set K : Submodule ℝ (Lp ℝ 2 (ν : Measure V)) :=
    Submodule.map Ψ (Submodule.comap ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain.subtype (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)) with hK
  -- the orthogonal complement of the range is trivial
  have hKorth : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
          ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
            (ν : Measure V))), u⟫ = 0 := by
      intro f hf hfc
      have hmemK : Ψ ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ ∈ K :=
        Submodule.mem_map_of_mem ⟨f, hf, hfc, rfl⟩
      have h0 := (Submodule.mem_orthogonal K u).mp hu _ hmemK
      rw [hΨapply, inner_add_left] at h0
      exact h0
    exact FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity_readable m hν hi hνU hU u horth (hreg u horth)
  have hdense : Dense (K : Set (Lp ℝ 2 (ν : Measure V))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr hKorth)
  obtain ⟨x, hxK, hxlim⟩ := mem_closure_iff_seq_limit.mp (hdense (Ψ F))
  have hchoice : ∀ n, ∃ z : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain, (z : (Lp ℝ 2
      (ν : Measure V))) ∈ FunctionalInequalities.Energy.WeightedGradient.smoothCore ν ∧ Ψ z = x n := by
    intro n
    obtain ⟨z, hzmem, hzeq⟩ := hxK n
    exact ⟨z, hzmem, hzeq⟩
  choose z hzs hzeq using hchoice
  have hzsm : ∀ n, ∃ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      (z n : (Lp ℝ 2 (ν : Measure V))) =
        (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f := hzs
  choose fn hfn hfnc hfneq using hzsm
  -- the graph-norm comparison
  have hcmp : ∀ n, ‖(z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2
    (ν : Measure V)))‖ ≤ ‖x n - Ψ F‖ ∧
      ‖((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) :
        (Lp ℝ 2 (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
            (ν : Measure V)))‖ ≤ ‖x n - Ψ F‖ := by
    intro n
    have hv : Ψ (z n - F) = x n - Ψ F := by rw [map_sub, hzeq n]
    have hcoe : ((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
        (ν : Measure V))) = (z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V))) := rfl
    have hAsub : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
        (ν : Measure V))) = ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) : (Lp ℝ 2
            (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
                (ν : Measure V))) :=
      LinearPMap.map_sub _ _ _
    have hnn : 0 ≤ ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
        (ν : Measure V))), ((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
            (ν : Measure V)))⟫ := by
      rw [FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_self hd (z n - F)]
      positivity
    have hexp : ‖Ψ (z n - F)‖ ^ 2 = ‖((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
        (ν : Measure V)))‖ ^ 2 +
        2 * ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
            (ν : Measure V))), ((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
                (ν : Measure V)))⟫ +
        ‖((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
            (ν : Measure V)))‖ ^ 2 := by
      rw [hΨapply]
      exact norm_add_sq_real _ _
    rw [hAsub, hcoe] at hnn
    rw [hv, hcoe, hAsub] at hexp
    constructor
    · nlinarith [hexp, hnn, norm_nonneg (x n - Ψ F), norm_nonneg ((z n : (Lp ℝ 2
      (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))),
        norm_nonneg (((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) : (Lp ℝ 2
            (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
                (ν : Measure V))))]
    · nlinarith [hexp, hnn, norm_nonneg (x n - Ψ F), norm_nonneg ((z n : (Lp ℝ 2
      (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))),
        norm_nonneg (((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) : (Lp ℝ 2
            (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
                (ν : Measure V))))]
  have hlim0 : Tendsto (fun n => ‖x n - Ψ F‖) atTop (𝓝 0) := by
    have := (hxlim.sub (tendsto_const_nhds (x := Ψ F))).norm
    simpa using this
  have hzeq' : ∀ n, (⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
      (hfnc n)⟩ : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) = z n := fun n => Subtype.ext (hfneq n).symm
  refine ⟨fn, hfn, hfnc, ?_, ?_⟩
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    rw [← hfneq n]
    exact (hcmp n).1
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    rw [hzeq' n]
    exact (hcmp n).2
