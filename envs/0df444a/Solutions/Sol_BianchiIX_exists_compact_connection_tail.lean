-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_tail
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:07:44.723196+00:00
-- url     : https://prove2.me/submissions/a98e1fe4-d185-4a4c-a9a6-e623174b8488

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_exists_compact_core_tail_two_germ
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


/-- The compact-connection range of B.7 has an actual finite downward tail with uniform C2 bounds. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧
        |coreTailTime η Y| + ‖coreTailState η Y‖ +
          ‖fderiv ℝ (coreTailTime η) Y‖ + ‖fderiv ℝ (coreTailState η) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailTime η)) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailState η)) Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_tail_two_germ (a := 31 / 8) (b := 6)
    (by norm_num) ⟨hη.1, by linarith only [hη.2]⟩
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have HY := H Y hk hu hw
  exact ⟨HY.1, HY.2.1, HY.2.2.1, HY.2.2.2.1⟩
