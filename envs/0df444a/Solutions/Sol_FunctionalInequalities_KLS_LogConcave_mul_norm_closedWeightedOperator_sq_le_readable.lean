-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:49.954441+00:00
-- url     : https://prove2.me/submissions/80b7858e-58a8-48d1-81d5-1253702dcd60

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_mul_norm_closedWeightedOperator_toLp_sq_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section
open FunctionalInequalities.Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
variable (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- **The Dirichlet form of the heat semigroup is the closed energy**: for `f ∈ D(T̄†T̄)`,
`⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`, and by `weighted_relaxation_of_mem` the right-hand side is the sequential
relaxation of `‖B ∇g‖²` at `f`. -/
theorem FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) :
    ⟪adjointComp (hν.closedWeightedOperator m B hi) f, (f : Lp ℝ 2 (ν : Measure V))⟫ =
      ‖hν.closedWeightedOperator m B hi ⟨f, f.2.2⟩‖ ^ 2 := by
  rw [inner_adjointComp (hν.dense_domain_closedWeightedOperator m B hi) f f.2.2,
    real_inner_self_eq_norm_sq]
end FullDimensional
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
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- The curvature bound on the whole operator domain: if `∇∇U ≥ ρ`, then `ρ ‖T̄ y‖² ≤ ‖A y‖²`
for every `y ∈ D(A)`. -/
theorem solution {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  have hinner
      (x : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) :
      ‖T ⟨x, x.2.2⟩‖ ^ 2 = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T x, x⟫_ℝ := by
    symm
    exact FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq m (ContinuousLinearMap.id ℝ V) hν hi x

  obtain ⟨fn, hfn, hfnc, h1, h2⟩ :=
    hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU.of_succ F

  let Fn : ℕ → (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain := fun n =>
    ⟨(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport (ν := ν) (hfn n)
        (hfnc n)).toLp (fn n),
      hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ
        (hfn n) (hfnc n)⟩

  have hle : ∀ n,
      ρ * ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T (Fn n), Fn n⟫_ℝ ≤
        ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T (Fn n)‖ ^ 2 := by
    intro n
    rw [← hinner (Fn n)]
    exact
      FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_toLp_sq_le_readable m hν hi hνU hU hH
        (hfn n) (hfnc n)

  have hFn :
      Tendsto
        (fun n =>
          ((Fn n : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) : Lp ℝ 2 (ν : Measure V)))
        atTop
        (𝓝 ((F : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Fn, T] using h1

  have hAF :
      Tendsto
        (fun n => FunctionalInequalities.Analysis.Semigroup.adjointComp T (Fn n))
        atTop
        (𝓝 (FunctionalInequalities.Analysis.Semigroup.adjointComp T F)) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Fn, T] using h2

  have hleft :
      Tendsto
        (fun n =>
          ρ * ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T (Fn n),
            ((Fn n : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) :
              Lp ℝ 2 (ν : Measure V))⟫_ℝ)
        atTop
        (𝓝
          (ρ * ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T F,
            ((F : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) :
              Lp ℝ 2 (ν : Measure V))⟫_ℝ)) := by
    simpa using
      (tendsto_const_nhds.mul (hAF.inner hFn))

  have hright :
      Tendsto
        (fun n => ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T (Fn n)‖ ^ 2)
        atTop
        (𝓝 (‖FunctionalInequalities.Analysis.Semigroup.adjointComp T F‖ ^ 2)) := by
    simpa using hAF.norm.pow 2

  have hlim :
      ρ * ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T F,
        ((F : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) :
          Lp ℝ 2 (ν : Measure V))⟫_ℝ ≤
        ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T F‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hleft hright hle

  change
    ρ * ‖T ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T F‖ ^ 2

  calc
    ρ * ‖T ⟨F, F.2.2⟩‖ ^ 2 =
        ρ * ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T F,
          ((F : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) :
            Lp ℝ 2 (ν : Measure V))⟫_ℝ := by
      rw [hinner F]
    _ ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T F‖ ^ 2 := hlim
