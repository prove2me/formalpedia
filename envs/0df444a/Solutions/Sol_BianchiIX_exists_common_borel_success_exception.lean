-- Prove2me | solution 1 for BianchiIX.exists_common_borel_success_exception
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:20:37.255064+00:00
-- url     : https://prove2.me/submissions/ac2c14bf-a56c-4cea-be6b-a09e3fada4a6

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_Literature_BrehmIXAttractorInput_wallProductDecay
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_ae_primaryAxis_success_of_decay
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_arbitrarily_late_primaryAxis_crossing
import Theorems.Thm_BianchiIX_exists_primaryAxis_saturated_null_exception
import Theorems.Thm_BianchiIX_isOpen_positiveWalls
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_rebase
import Theorems.Thm_BianchiIX_nullInFourCoordinates_geometricException
import Theorems.Thm_BianchiIX_volume_preimage_geometricException
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taubRadiusSq_nonneg (s b c : ℝ) : 0 ≤ taubRadiusSq s b c :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.NullInFourCoordinates.union {S T : Set NormalizedState}
    (HS : NullInFourCoordinates S) (HT : NullInFourCoordinates T) :
    NullInFourCoordinates (S ∪ T) := by
  intro P hP
  rw [image_union]
  exact measure_union_null (HS P hP) (HT P hP)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_mainWallRadicand (h : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (mainWallRadicand h) := by
  unfold mainWallRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_mainWallChartDomain (h : ℝ) : IsOpen (mainWallChartDomain h) :=
  isOpen_lt continuous_const (contDiff_mainWallRadicand h 1).continuous

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedMaxCurve_inverse {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    -t ∈ normalizedMaxDomain (normalizedMaxCurve x 0 t) 0 ∧
      normalizedMaxCurve (normalizedMaxCurve x 0 t) 0 (-t) = x := by
  have hzero : 0 ∈ normalizedMaxDomain (normalizedMaxCurve x 0 t) t := by
    rw [normalizedMaxDomain_rebase ht]
    exact initial_mem_normalizedMaxDomain x 0
  refine ⟨(mem_normalizedMaxDomain_retime (t₀ := t)).mpr (by simpa using hzero), ?_⟩
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using ht)
    (show -t + t ∈ normalizedMaxDomain x 0 by simpa using initial_mem_normalizedMaxDomain x 0)
  simpa only [zero_add, neg_add_cancel, normalizedMaxCurve_initial] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.NormalizedSymmetry.fixed_maxCurve_iff (A : NormalizedSymmetry)
    {x : NormalizedState} {t₀ t : ℝ} (ht : t ∈ normalizedMaxDomain x t₀) :
    A.map (normalizedMaxCurve x t₀ t) = normalizedMaxCurve x t₀ t ↔ A.map x = x := by
  constructor
  · intro heq
    have hAt : t ∈ normalizedMaxDomain (A.map x) t₀ := by rwa [A.maxDomain]
    calc
      A.map x = normalizedMaxCurve (normalizedMaxCurve (A.map x) t₀ t) t t₀ := by
        rw [normalizedMaxCurve_rebase hAt (initial_mem_normalizedMaxDomain _ _), normalizedMaxCurve_initial]
      _ = normalizedMaxCurve (normalizedMaxCurve x t₀ t) t t₀ := by rw [A.maxCurve ht, heq]
      _ = x := by rw [normalizedMaxCurve_rebase ht (initial_mem_normalizedMaxDomain _ _), normalizedMaxCurve_initial]
  · intro heq
    rw [← A.maxCurve ht, heq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubRadiusSq_eq_zero_iff (x : NormalizedState) :
    normalizedTaubRadiusSq x = 0 ↔ axisSwap x = x := by
  constructor
  · intro hr
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hr
    have hs : x 1 = 0 := by nlinarith [sq_nonneg (x 3 - x 4)]
    have hw : x 3 = x 4 := by nlinarith [sq_nonneg (x 1)]
    ext i
    fin_cases i <;> simp [axisSwap, hs, hw]
  · intro heq
    have hs := congrFun heq 1
    have hw := congrFun heq 3
    change -x 1 = x 1 at hs
    change x 4 = x 3 at hw
    dsimp [normalizedTaubRadiusSq, taubRadiusSq]
    rw [hw]
    nlinarith only [hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_normalizedEuclideanDistance :
    Continuous (fun p : NormalizedState × NormalizedState => normalizedEuclideanDistance p.1 p.2) := by
  unfold normalizedEuclideanDistance
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.measurableSet_physicalPhaseSpace : MeasurableSet physicalPhaseSpace :=
  isOpen_positiveWalls.measurableSet.inter
    (isClosed_eq (contDiff_stateConstraint 1).continuous continuous_const).measurableSet

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.mem_physicalPhaseSpace_maxCurve_iff {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 t ∈ physicalPhaseSpace ↔ x ∈ physicalPhaseSpace := by
  constructor
  · intro hx
    have H := (maximalNormalizedSolution (normalizedMaxCurve x 0 t) 0).physical
      hx.1 hx.2 (normalizedMaxCurve_inverse ht).1
    change normalizedMaxCurve (normalizedMaxCurve x 0 t) 0 (-t) ∈ physicalPhaseSpace at H
    rwa [(normalizedMaxCurve_inverse ht).2] at H
  · intro hx
    exact (maximalNormalizedSolution x 0).physical hx.1 hx.2 ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.continuous_physical_forwardFlow {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun x : physicalPhaseSpace => normalizedMaxCurve x.val 0 t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hF := (normalizedMaxCurve_regular
    (normalizedMaxDomain_contains_Ici_of_constraint x.property.2 0 ht)).2.continuousAt
  have hG : ContinuousAt (fun y : physicalPhaseSpace => (y.val, t)) x :=
    continuous_subtype_val.continuousAt.prodMk continuous_const.continuousAt
  have H := hF.comp (f := fun y : physicalPhaseSpace => (y.val, t)) hG
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.isClosed_taubSubspaces : IsClosed taubSubspaces := by
  have heq : taubSubspaces = ⋃ i : Fin 3,
      {x | normalizedTaubRadiusSq ((primaryAxisFrame i).map x) = 0} := by
    ext x; simp [taubSubspaces]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_eq _ continuous_const
  unfold normalizedTaubRadiusSq taubRadiusSq
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.mem_taubSubspaces_maxCurve_iff {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 t ∈ taubSubspaces ↔ x ∈ taubSubspaces := by
  unfold taubSubspaces
  change (∃ i, normalizedTaubRadiusSq ((primaryAxisFrame i).map (normalizedMaxCurve x 0 t)) = 0) ↔ _
  apply exists_congr
  intro i
  have hdom : t ∈ normalizedMaxDomain ((primaryAxisFrame i).map x) 0 := by
    rwa [(primaryAxisFrame i).maxDomain]
  rw [← (primaryAxisFrame i).maxCurve ht, normalizedTaubRadiusSq_eq_zero_iff,
    normalizedTaubRadiusSq_eq_zero_iff]
  exact NormalizedSymmetry.swap.fixed_maxCurve_iff hdom

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.not_mem_taubSubspaces_iff (x : NormalizedState) :
    x ∉ taubSubspaces ↔ ∀ i, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x) := by
  simp only [taubSubspaces, mem_ofPred_eq, not_exists]
  apply forall_congr'
  intro i
  constructor
  · intro h
    exact lt_of_le_of_ne (taubRadiusSq_nonneg _ _ _) (Ne.symm h)
  · exact ne_of_gt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.wallProductDecay_maxCurve_iff {x : NormalizedState} {s : ℝ}
    (hc : stateConstraint x = 1) (hs : s ∈ normalizedMaxDomain x 0) :
    WallProductDecay (normalizedMaxCurve x 0 s) ↔ WallProductDecay x := by
  unfold WallProductDecay
  refine forall_congr' (fun i => forall_congr' (fun j => forall_congr' (fun _ => ?_)))
  have heq :
      (fun t => wallValue i (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 t) *
        wallValue j (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 t)) =ᶠ[atTop]
      (fun t => wallValue i (normalizedMaxCurve x 0 (t + s)) *
        wallValue j (normalizedMaxCurve x 0 (t + s))) := by
    filter_upwards [eventually_ge_atTop (-s)] with t ht
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (show 0 ≤ t + s by linarith)
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hs) hdom
    simpa only [zero_add] using congrArg (fun z => wallValue i z * wallValue j z) H
  rw [tendsto_congr' heq]
  change Tendsto ((fun t => wallValue i (normalizedMaxCurve x 0 t) *
    wallValue j (normalizedMaxCurve x 0 t)) ∘ (fun t => t + s)) atTop (𝓝 0) ↔ _
  rw [← tendsto_map'_iff, map_add_atTop_eq]

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.eventuallyTaubSeparated_iff_countable (x : NormalizedState) :
    EventuallyTaubSeparated x ↔ ∃ n m : ℕ, ∀ t : ℝ, (m : ℝ) ≤ t → ∀ i : Fin 3,
      1 / (n + 1 : ℝ) ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) := by
  constructor
  · rintro ⟨ε, hε, H⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp H
    obtain ⟨m, hm⟩ := exists_nat_ge T
    exact ⟨n, m, fun t ht i => hn.le.trans (hT t (hm.trans ht) i)⟩
  · rintro ⟨n, m, H⟩
    exact ⟨1 / (n + 1 : ℝ), by positivity,
      (eventually_ge_atTop (m : ℝ)).mono fun t ht => H t ht⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.measurableSet_physical_eventuallyTaubSeparated :
    MeasurableSet {x | x ∈ physicalPhaseSpace ∧ EventuallyTaubSeparated x} := by
  let S : Set physicalPhaseSpace := {x | EventuallyTaubSeparated x.val}
  have hS : MeasurableSet S := by
    have heq : S = ⋃ n : ℕ, ⋃ m : ℕ, ⋂ t : ℝ, ⋂ (_ : (m : ℝ) ≤ t), ⋂ i : Fin 3,
        {x : physicalPhaseSpace | 1 / (n + 1 : ℝ) ≤
          normalizedEuclideanDistance (normalizedMaxCurve x.val 0 t) (taubPoint i)} := by
      ext x
      simp only [S, mem_ofPred_eq, mem_iUnion, mem_iInter,
        eventuallyTaubSeparated_iff_countable]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro m
    apply IsClosed.measurableSet
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro ht
    apply isClosed_iInter
    intro i
    have hf := continuous_physical_forwardFlow ((Nat.cast_nonneg m).trans ht)
    have hd := continuous_normalizedEuclideanDistance.comp
      (hf.prodMk (continuous_const : Continuous (fun _ : physicalPhaseSpace => taubPoint i)))
    exact isClosed_le (continuous_const : Continuous (fun _ : physicalPhaseSpace => 1 / (n + 1 : ℝ))) hd
  have H := measurableSet_physicalPhaseSpace.subtype_image hS
  convert H using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, S, Subtype.exists, exists_and_right, exists_eq_right, exists_prop]

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.eventuallyTaubSeparated_maxCurve_iff {x : NormalizedState} {s : ℝ}
    (hc : stateConstraint x = 1) (hs : s ∈ normalizedMaxDomain x 0) :
    EventuallyTaubSeparated (normalizedMaxCurve x 0 s) ↔ EventuallyTaubSeparated x := by
  unfold EventuallyTaubSeparated
  apply exists_congr
  intro ε
  apply and_congr_right
  intro _
  have heq : (fun t => ∀ i, ε ≤ normalizedEuclideanDistance
        (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 t) (taubPoint i)) =ᶠ[atTop]
      (fun t => ∀ i, ε ≤ normalizedEuclideanDistance
        (normalizedMaxCurve x 0 (t + s)) (taubPoint i)) := by
    filter_upwards [eventually_ge_atTop (-s)] with t ht
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (show 0 ≤ t + s by linarith)
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hs) hdom
    simp only [zero_add] at H
    rw [H]
  rw [eventually_congr (heq.mono fun _ h => h.to_iff)]
  have H := (eventually_map (f := atTop) (m := fun t : ℝ => t + s)
    (P := fun t => ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)))
  rw [map_add_atTop_eq] at H
  exact H.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.not_eventuallyTaubSeparated_iff (x : NormalizedState) :
    ¬EventuallyTaubSeparated x ↔ ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) < ε := by
  constructor
  · intro H ε hε R
    by_contra! hn
    exact H ⟨ε, hε, (eventually_ge_atTop R).mono fun t ht i => hn t ht i⟩
  · rintro H ⟨ε, hε, Ha⟩
    obtain ⟨T, hT⟩ := eventually_atTop.mp Ha
    obtain ⟨t, ht, i, hi⟩ := H ε hε T
    exact (not_lt_of_ge (hT t ht i)) hi

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.measurableSet_geometricException : MeasurableSet geometricException := by
  have heq : geometricException = (physicalPhaseSpace ∩ taubSubspaces) ∪
      {x | x ∈ physicalPhaseSpace ∧ EventuallyTaubSeparated x} := by
    ext x; simp [geometricException, and_or_left]
  rw [heq]
  exact (measurableSet_physicalPhaseSpace.inter isClosed_taubSubspaces.measurableSet).union
    measurableSet_physical_eventuallyTaubSeparated

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.mem_geometricException_maxCurve_iff {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 t ∈ geometricException ↔ x ∈ geometricException := by
  simp only [geometricException, mem_ofPred_eq, mem_physicalPhaseSpace_maxCurve_iff ht,
    mem_taubSubspaces_maxCurve_iff ht]
  apply and_congr_right
  intro hx
  rw [eventuallyTaubSeparated_maxCurve_iff hx.2 ht]

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.arbitrarily_late_taub_approach_of_not_mem_geometricException
    {x : NormalizedState} (hx : x ∈ physicalPhaseSpace) (hN : x ∉ geometricException) :
    (∀ i, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x)) ∧
      ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
        normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) < ε := by
  exact ⟨(not_mem_taubSubspaces_iff x).mp (fun hT => hN ⟨hx, Or.inl hT⟩),
    (not_eventuallyTaubSeparated_iff x).mp (fun hT => hN ⟨hx, Or.inr hT⟩)⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallSmallSection (d : ℝ) : MeasurableSet (mainWallSmallSection d) := by
  have hs : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have hm : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_le hs measurable_const).inter (measurableSet_le hm measurable_const)

end
end

private theorem BianchiIX.globalAxisWallHittingDomain_of_forward {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {x : NormalizedState} {s : ℝ}
    (hs : 0 ≤ s) (hdom : s ∈ normalizedMaxDomain x 0)
    (H : normalizedMaxCurve x 0 s ∈ globalAxisWallHittingDomain A h B (Ici 0)) :
    x ∈ globalAxisWallHittingDomain A h B (Ici 0) := by
  obtain ⟨t, ht, htdom, i, y, hy, heq⟩ := H
  have Hflow := normalizedMaxCurve_restart (t := t + s) hdom (by simpa using htdom)
  simp only [add_sub_cancel_right] at Hflow
  exact ⟨t + s, add_nonneg ht hs, Hflow.1, i, y, hy, heq.trans Hflow.2.symm⟩


/-- The fixed success target is reached outside one invariant exception, null in both physical dimensions. -/
theorem solution
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    {F : Set (Fin 3 × SectionCoordinates)} (hF : MeasurableSet F)
    (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤) :
    let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
    ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
      geometricException ⊆ N ∧
      (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
        normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
      (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
        IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
        (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
        (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
        volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
      ∀ x ∈ physicalPhaseSpace, x ∉ N →
        x ∈ globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
          (axisFamilySuccessTargets E F) (Ici 0) := by
  intro E
  obtain ⟨S, hSm, hSp, hSi, hSn, hSfour, hsuccess⟩ := exists_primaryAxis_saturated_null_exception hh
    (fun _ => (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet)
    (fun _ _ hz => hz.2) (ae_primaryAxis_success_of_decay hBirkhoff hh hhmax hd hdh hF hfinite)
  let N := S ∪ geometricException
  refine ⟨N, hSm.union measurableSet_geometricException, ?_, subset_union_right, ?_, ?_,
    hSfour.union (nullInFourCoordinates_geometricException hBirkhoff hBrehm), ?_⟩
  · intro x hx
    exact hx.elim (hSp x) And.left
  · intro x t ht
    simp only [N, mem_union, hSi x t ht, mem_geometricException_maxCurve_iff ht]
  · intro C U hU hC hp hc hflux
    have heq : U ∩ C ⁻¹' N = (U ∩ C ⁻¹' S) ∪ (U ∩ C ⁻¹' geometricException) := by
      ext y; simp [N, and_or_left]
    rw [heq]
    exact measure_union_null (hSn C U hU hC hp hc hflux)
      (volume_preimage_geometricException hBirkhoff hBrehm hU hC hp hc hflux)
  · intro x hx hn
    have hns : x ∉ S := fun hS => hn (Or.inl hS)
    have hng : x ∉ geometricException := fun hG => hn (Or.inr hG)
    have hT : x ∉ taubSubspaces := fun hT => hng ⟨hx, Or.inl hT⟩
    have hprod := hBrehm.wallProductDecay hx hT
    obtain ⟨hr, hvisit⟩ := arbitrarily_late_taub_approach_of_not_mem_geometricException hx hng
    obtain ⟨i, hi⟩ := exists_arbitrarily_late_primaryAxis_crossing hx.2 hx.1 hr hh hhmax hd hdh hprod hvisit
    obtain ⟨t, ht, hdom, y, hy, heq, hs, hb, hw, _⟩ := hi 0 1 (by norm_num)
    have hys : axisWallChart (primaryAxisFrame i) h y ∉ S := by
      rw [heq, hSi x t hdom]
      exact hns
    have hyp : WallProductDecay (axisWallChart (primaryAxisFrame i) h y) := by
      rw [heq, wallProductDecay_maxCurve_iff hx.2 hdom]
      exact hprod
    have H := hsuccess (i, y) ⟨⟨hs.le, max_le hb.le hw.le⟩, hy⟩ hys hyp
    apply globalAxisWallHittingDomain_of_forward primaryAxisFrame (by simpa using ht.le) hdom
    simpa only [axisFamilyChart, heq] using H
