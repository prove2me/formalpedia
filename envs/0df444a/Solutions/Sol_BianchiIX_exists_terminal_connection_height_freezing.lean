-- Prove2me | solution 1 for BianchiIX.exists_terminal_connection_height_freezing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:13:51.66967+00:00
-- url     : https://prove2.me/submissions/e91c128d-d483-415c-b6d5-93b057952abd

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_TerminalConnectionData
import Theorems.Thm_BianchiIX_exists_terminal_connection_joint_height_regular
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

private theorem BianchiIX.terminalConnection_freeze_height_of_local {h : ℝ} {Y : CoreAngleState}
    (HT : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y))
    (HS : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y))
    (HL : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
      terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
      terminalConnectionState p.1 p.2 = terminalConnectionState h p.2)
    {a : CoreAngleState → ℝ} (ha : ContinuousAt a Y) (haY : a Y = h) :
    (∀ᶠ Z in 𝓝 Y, terminalConnectionTime (a Z) Z = terminalConnectionTime h Z ∧
      terminalConnectionState (a Z) Z = terminalConnectionState h Z) ∧
      ContDiffAt ℝ 2 (fun Z => terminalConnectionTime (a Z) Z) Y ∧
      ContDiffAt ℝ 2 (fun Z => terminalConnectionState (a Z) Z) Y := by
  have hgraph : Tendsto (fun Z => (a Z, Z)) (𝓝 Y) (𝓝 (h, Y)) := by
    simpa only [ContinuousAt, haY, id_eq] using ha.prodMk continuousAt_id
  have HE := hgraph.eventually HL
  have hfixed : ContDiffAt ℝ 2 (fun Z : CoreAngleState => (h, Z)) Y := contDiffAt_const.prodMk contDiffAt_id
  exact ⟨HE, (HT.comp Y hfixed).congr_of_eventuallyEq (HE.mono fun _ hp => hp.1),
    (HS.comp Y hfixed).congr_of_eventuallyEq (HE.mono fun _ hp => hp.2)⟩

private theorem BianchiIX.terminalConnection_height_deriv_zero_of_local {h : ℝ} {Y : CoreAngleState}
    (HL : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
      terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
      terminalConnectionState p.1 p.2 = terminalConnectionState h p.2) :
    HasDerivAt (fun v => terminalConnectionTime v Y) 0 h ∧
      HasDerivAt (fun v => terminalConnectionState v Y) 0 h := by
  have hslice : ContinuousAt (fun v : ℝ => (v, Y)) h := continuousAt_id.prodMk continuousAt_const
  have HE := hslice.eventually HL
  exact ⟨(hasDerivAt_const h (terminalConnectionTime h Y)).congr_of_eventuallyEq
      (HE.mono fun _ hp => hp.1),
    (hasDerivAt_const h (terminalConnectionState h Y)).congr_of_eventuallyEq
      (HE.mono fun _ hp => hp.2)⟩


/-- On the actual domain every continuous height selection has the same C2 germ as the frozen map. -/
theorem solution {εin η : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      HasDerivAt (fun v => terminalConnectionTime v Y) 0 h ∧
        HasDerivAt (fun v => terminalConnectionState v Y) 0 h ∧
        ∀ a : CoreAngleState → ℝ, ContinuousAt a Y → a Y = h →
          (∀ᶠ Z in 𝓝 Y, terminalConnectionTime (a Z) Z = terminalConnectionTime h Z ∧
            terminalConnectionState (a Z) Z = terminalConnectionState h Z) ∧
          ContDiffAt ℝ 2 (fun Z => terminalConnectionTime (a Z) Z) Y ∧
          ContDiffAt ℝ 2 (fun Z => terminalConnectionState (a Z) Z) Y := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_connection_joint_height_regular hεin hη hJ hηin
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h
  obtain ⟨HT, HS, HL⟩ := HE α b u w hα hb hsmall hsum hu hw
  have HD := terminalConnection_height_deriv_zero_of_local HL
  exact ⟨HD.1, HD.2, fun a ha haY => terminalConnection_freeze_height_of_local HT HS HL ha haY⟩
