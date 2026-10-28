-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_toLp_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:39.997377+00:00
-- url     : https://prove2.me/submissions/1b23b169-5251-4685-a9cf-f08ca58e9917

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_mul_integral_gamma_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_gradient_sq_readable

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
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- The curvature bound on smooth compactly supported classes: if `∇∇U ≥ ρ`, then
`ρ ‖T̄ [f]‖² ≤ ‖A [f]‖²`. -/
theorem solution {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
      ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ hf hfc⟩‖ ^ 2 := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    hν.adjointComp_toLp_eq m hi hνU hU.of_succ hf hfc]

  have hneg :
      ‖(FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := ν) hU.of_succ hf hfc).toLp
          (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x)‖ ^ 2 =
        ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂(ν : Measure V) := by
    let hL := FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := ν) hU.of_succ hf hfc
    change ‖hL.toLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x)‖ ^ 2 =
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂(ν : Measure V)
    calc
      ‖hL.toLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x)‖ ^ 2 =
          ⟪hL.toLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x),
            hL.toLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x)⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      _ = ∫ x, ⟪-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x,
            -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x⟫_ℝ ∂(ν : Measure V) := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hL] with x hx
        rw [hx]
      _ = ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂(ν : Measure V) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [real_inner_self_eq_norm_sq, norm_neg, Real.norm_eq_abs,
          sq_abs]

  rw [FunctionalInequalities.KLS.LogConcave.norm_toLp_gradient_sq_readable (ν := ν) hf hfc, hneg, hνU]
  exact FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le_readable m hU
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc hH
