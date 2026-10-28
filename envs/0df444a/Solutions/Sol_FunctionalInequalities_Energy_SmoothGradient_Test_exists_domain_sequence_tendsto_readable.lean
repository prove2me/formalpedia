-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:30.811423+00:00
-- url     : https://prove2.me/submissions/7caf2298-1e76-40ca-9225-b4b916a29888

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_LocalDensity_subset_support_readable

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section
variable {ν : MeasureTheory.ProbabilityMeasure V} {m : MeasureTheory.Measure V} (D : FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m)
variable [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- `Ω` lies in the interior of the support. -/
theorem FunctionalInequalities.Energy.SmoothGradient.LocalDensity.subset_interior_support : D.Ω ⊆ interior (ν : Measure V).support :=
  interior_maximal D.subset_support_readable D.isOpen
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
include D in
/-- The frontier of the support is `ν`-null. -/
theorem FunctionalInequalities.Energy.SmoothGradient.LocalDensity.frontier_support_null : (ν : Measure V) (frontier (ν : Measure V).support) = 0 := by
  refine measure_mono_null ?_ D.compl_null
  intro x hx hxΩ
  rw [Measure.isClosed_support.frontier_eq] at hx
  exact hx.2 (D.subset_interior_support hxΩ)
end
section Agreement
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (D : FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m)
open FunctionalInequalities.Energy.WeightedGradient FunctionalInequalities.Energy.Euclidean
/-- Smooth cutoffs: every smooth test is the graph-norm limit of globally Lipschitz compactly
supported tests, as elements of the operator domain. -/
theorem solution (f : FunctionalInequalities.Energy.SmoothGradient.Test ν) :
    ∃ p : ℕ → (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D).domain,
      Tendsto (fun j ↦ (((p j : (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)),
        FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D (p j))) atTop
        (𝓝 (f.toL2, (FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f).toLp (gradient f.toFun))) := by
  have hac := D.absolutelyContinuous
  have hfr := D.frontier_support_null
  have hlip : LocallyLipschitz f.toFun := (f.contDiff.of_le (by exact_mod_cast le_top)).locallyLipschitz
  have hgrad : MemLp (fun x ↦ (ContinuousLinearMap.id ℝ V) (gradient f.toFun x)) 2 (ν : Measure V) := by
    simpa using FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f
  obtain ⟨g, hg, hconv1, hconv2⟩ := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_compactSupport_weighted_L2 ν m hac
    (ContinuousLinearMap.id ℝ V) f.toFun hlip f.memLp_two hgrad
  have hIsTest : ∀ j, FunctionalInequalities.Energy.WeightedGradient.IsTest ν (ContinuousLinearMap.id ℝ V) (g j) := fun j ↦
    ⟨(hg j).2.1, (hg j).2.2.1, (hg j).2.2.2⟩
  refine ⟨fun j ↦ ⟨(hIsTest j).memLp.toLp (g j),
    FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) hac (hIsTest j)⟩, ?_⟩
  have hT : ∀ j, FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D ⟨(hIsTest j).memLp.toLp (g j),
      FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) hac (hIsTest j)⟩ =
      (hIsTest j).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (g j)) := fun j ↦
    FunctionalInequalities.Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr (hIsTest j) _ rfl
  refine Filter.Tendsto.prodMk_nhds ?_ ?_
  · rw [tendsto_iff_dist_tendsto_zero]
    have h : ∀ j, dist ((hIsTest j).memLp.toLp (g j)) f.toL2 =
        (eLpNorm (fun x ↦ g j x - f.toFun x) 2 (ν : Measure V)).toReal := by
      intro j
      rw [dist_edist, FunctionalInequalities.Energy.SmoothGradient.Test.toL2, Lp.edist_toLp_toLp]
      rfl
    simp_rw [h]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv1
    simpa [Function.comp_def] using this
  · simp_rw [hT]
    rw [tendsto_iff_dist_tendsto_zero]
    have h : ∀ j, dist ((hIsTest j).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (g j)))
        ((FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f).toLp (gradient f.toFun)) =
        (eLpNorm (fun x ↦ (ContinuousLinearMap.id ℝ V) (gradient (g j) x) -
          (ContinuousLinearMap.id ℝ V) (gradient f.toFun x)) 2 (ν : Measure V)).toReal := by
      intro j
      rw [dist_edist, Lp.edist_toLp_toLp]
      rfl
    simp_rw [h]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv2
    simpa [Function.comp_def] using this
