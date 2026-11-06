-- Prove2me | solution 1 for BianchiIX.exists_terminal_connection_joint_height_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:12:25.37766+00:00
-- url     : https://prove2.me/submissions/4f1b9bd3-5d44-4f30-a22a-46b2690fd674

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_exists_terminal_cycle_entrance_inputs
import Theorems.Thm_BianchiIX_terminalConnection_joint_regular_height_independent
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology



/-- The actual positive-wall terminal domain satisfies the joint local height theorem. -/
theorem solution {εin η : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y) ∧
        ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y) ∧
        (∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
          terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
          terminalConnectionState p.1 p.2 = terminalConnectionState h p.2) := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_cycle_entrance_inputs hεin.1 hη hJ hηin
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h
  obtain ⟨HV, _, HK, HM, HU, HVa, HW, HF, HH⟩ := HE α b u w hα hb hsmall hsum hu hw
  let z := projectiveCycle (coreTailState h Y)
  have hk1 : 1 ≤ coreRadius (z 0) (z 2) := by linarith only [HK]
  have hpow : 1 ≤ coreRadius (z 0) (z 2) ^ q := one_le_pow₀ hk1
  have HU' : z 1 < 1 / 10000 := by
    have H := mul_le_mul_of_nonneg_left hpow HU.1.le
    nlinarith only [H, HU.2.2, hεin.2]
  have HW' : z 3 < 1 / 10000 := by
    have H := mul_le_mul_of_nonneg_left hpow HW.1.le
    nlinarith only [H, HW.2.2, hεin.2]
  exact terminalConnection_joint_regular_height_independent
    (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV HH
    (fun t ht => ⟨(HF t ht).1, by
      have Hb := (HF t ht).2
      change toProjectiveState _ 2 < 1
      linarith only [le_abs_self (toProjectiveState (normalizedMaxCurve
        (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t) 2), Hb]⟩)
    HK (by linarith only [HM]) ⟨HU.1, HU'⟩ ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1, HW'⟩
