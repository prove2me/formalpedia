-- Prove2me | solution 1 for BianchiIX.mainWallOriginalMeasure_closedFailure
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:06:01.199514+00:00
-- url     : https://prove2.me/submissions/72c1b43e-a909-4c96-8285-e4c3780b0eea

import Definitions.Def_BianchiIX_RadialFailureData
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_sectionCoordinate_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | z i = t} = 0 := by
  exact Measure.pi_eval_preimage_null (fun _ : Fin 3 => (volume : Measure ℝ)) (measure_singleton t)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_sectionWall_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | Real.exp (-z i) = t} = 0 := by
  apply measure_mono_null (t := {z : SectionCoordinates | z i = -Real.log t})
    _ (volume_sectionCoordinate_level i _)
  intro z hz
  have H := congrArg Real.log hz
  rw [Real.log_exp] at H
  change z i = -Real.log t
  linarith

end
end

private theorem BianchiIX.volume_mainWallSectionBoundary (d : ℝ) : volume (mainWallSectionBoundary d) = 0 := by
  have H : volume (({z : SectionCoordinates | z 0 = d} ∪ {z | z 0 = -d}) ∪
      ({z | Real.exp (-z 1) = d} ∪ {z | Real.exp (-z 2) = d})) = 0 :=
    measure_union_null (measure_union_null (volume_sectionCoordinate_level 0 d)
      (volume_sectionCoordinate_level 0 (-d)))
      (measure_union_null (volume_sectionWall_level 1 d) (volume_sectionWall_level 2 d))
  apply measure_mono_null _ H
  intro z hz
  by_cases hs : |z 0| < d
  · have hm : max (Real.exp (-z 1)) (Real.exp (-z 2)) = d :=
      le_antisymm hz.1.2 (le_of_not_gt (fun hm => hz.2 ⟨hs, hm⟩))
    apply Or.inr
    rcases le_total (Real.exp (-z 1)) (Real.exp (-z 2)) with hw | hw
    · exact Or.inr (by simpa only [mem_ofPred_eq, max_eq_right hw] using hm)
    · exact Or.inl (by simpa only [mem_ofPred_eq, max_eq_left hw] using hm)
  · have heq : |z 0| = d := le_antisymm hz.1.1 (le_of_not_gt hs)
    apply Or.inl
    rcases le_total 0 (z 0) with ht | ht
    · exact Or.inl (by simpa only [mem_ofPred_eq, abs_of_nonneg ht] using heq)
    · exact Or.inr (by rw [abs_of_nonpos ht] at heq; change z 0 = -d; linarith)

private theorem BianchiIX.mainWallOriginalMeasure_sectionBoundary (h d : ℝ) :
    mainWallOriginalMeasure h (mainWallSectionBoundary d) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  exact Measure.absolutelyContinuous_restrict (volume_mainWallSectionBoundary d)


theorem solution (h d : ℝ) (E : Set SectionCoordinates) :
    mainWallOriginalMeasure h (mainWallClosedFailure d E) = mainWallOriginalMeasure h E := by
  apply le_antisymm _ (measure_mono subset_union_right)
  exact (measure_union_le _ _).trans_eq (by rw [mainWallOriginalMeasure_sectionBoundary, zero_add])
