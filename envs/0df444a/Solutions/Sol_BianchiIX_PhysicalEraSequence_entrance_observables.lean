-- Prove2me | solution 1 for BianchiIX.PhysicalEraSequence.entrance_observables
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:06:51.206762+00:00
-- url     : https://prove2.me/submissions/a704e85e-ed13-4ad1-9b27-d88ffb0fbc12

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_PhysicalEraData
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.PhysicalEraSequence
variable {η : ℝ} {J : ℕ} {x : NormalizedState} {K : ℕ → ℕ+} {Y : ℕ → CoreAngleState}
variable {t : ℕ → ℝ} {a : ℕ → Fin 6} (H : PhysicalEraSequence η J x K Y t a)
include H

private theorem BianchiIX.PhysicalEraSequence.digit_eq_floor (n : ℕ) : (K n : ℕ) = Nat.floor (Y n 0 / 2) := by
  simpa only [PNat.natPred_add_one] using (H.block n).count.symm

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.PhysicalEraSequence
open Set
variable {η : ℝ} {J : ℕ} {x : NormalizedState} {K : ℕ → ℕ+} {Y : ℕ → CoreAngleState}
variable {t : ℕ → ℝ} {a : ℕ → Fin 6} (H : PhysicalEraSequence η J x K Y t a)
include H

private theorem BianchiIX.PhysicalEraSequence.projective_entrance (n : ℕ) :
    toProjectiveState ((axisFrame (a n)).map (normalizedMaxCurve x 0 (t n))) =
      coreRadiusEntry (Y n) := by
  have HV : coreRadiusReturnValid (Y n) := by
    simpa only [Function.iterate_zero_apply] using ((H.block n).core 0 (Nat.zero_le _)).2.2.1
  have hc : 0 < 1 + fromProjectiveState (coreRadiusEntry (Y n)) 0 := by
    simpa only [normalizedMaxCurve_initial] using (HV.2.1 0 ⟨le_rfl, HV.1.1.1.le⟩).2
  have hD : projectiveStateDenom (coreRadiusEntry (Y n)) ≠ 0 := by
    intro hz
    change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry (Y n)) - 1) at hc
    simp only [hz, div_zero, zero_sub, add_neg_cancel, lt_self_iff_false] at hc
  rw [← H.entrance n, toProjectiveState_fromProjectiveState hD]

end
end

noncomputable section
open BianchiIX
open BianchiIX.PhysicalEraSequence
open Set
variable {η : ℝ} {J : ℕ} {x : NormalizedState} {K : ℕ → ℕ+} {Y : ℕ → CoreAngleState}
variable {t : ℕ → ℝ} {a : ℕ → Fin 6} (H : PhysicalEraSequence η J x K Y t a)
include H



/-- The stored radius and phase are the geometric observables of the actual incoming section. -/
theorem solution (n : ℕ) :
    let z := toProjectiveState ((axisFrame (a n)).map (normalizedMaxCurve x 0 (t n)))
    z 2 = 1 ∧ Real.sqrt ((z 0 - 1) ^ 2 + 1) = Y n 0 ∧
      1 < Y n 0 / 2 ∧ 2 / Y n 0 ∈ Ioo (0 : ℝ) 1 ∧
      (K n : ℕ) = Nat.floor (Y n 0 / 2) := by
  have hk : 2 < Y n 0 := by
    simpa only [Function.iterate_zero_apply] using ((H.block n).core 0 (Nat.zero_le _)).1
  have hk0 : 0 < Y n 0 := lt_trans (by norm_num) hk
  rw [H.projective_entrance n]
  refine ⟨rfl, ?_, by linarith only [hk],
    ⟨div_pos (by norm_num) hk0, (div_lt_one hk0).mpr hk⟩, H.digit_eq_floor n⟩
  simpa only [coreRadius, coreEnergy, show coreRadiusEntry (Y n) 2 = 1 from rfl, one_pow] using
    coreRadius_coreRadiusEntry (Y := Y n) (lt_trans (by norm_num) hk)
