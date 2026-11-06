-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_large_walls
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:38:41.719119+00:00
-- url     : https://prove2.me/submissions/38e5e9ad-4732-4d1e-8252-361f8b689bf0

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_regular
import Theorems.Thm_BianchiIX_coreReturnMultiplier_contraction
import Theorems.Thm_BianchiIX_exists_large_core_multipliers
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (i : Fin 2) :
    let F := coreReturnState coreRadiusReturnTime Y
    0 ≤ F i.succ ∧ (0 < F i.succ ↔ 0 < Y i.succ) ∧
      F i.succ ≤ Real.exp (-1 / (2 * Y 0)) * Y i.succ := by
  intro F
  have hfirst := (coreRadiusReturn_large_regular hk hu hw).2.2.2.self_of_nhds
  obtain ⟨T, _, hT, hpos, hU, hW⟩ := exists_large_core_multipliers hk hu hw
  have ht : T = coreRadiusReturnTime Y := hT.unique hfirst
  subst T
  have hformula : F i.succ = Y i.succ * coreReturnMultiplier coreRadiusReturnTime Y i := by
    fin_cases i
    · exact hU
    · change projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y) 2 *
        projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y) 3 = _
      rw [hfirst.1.2, one_mul]
      exact hW
  have hi : 0 ≤ Y i.succ := by
    fin_cases i
    · exact hu.1
    · exact hw.1
  have hc := coreReturnMultiplier_contraction hk hu hw hfirst
  have hbound : coreReturnMultiplier coreRadiusReturnTime Y i ≤ Real.exp (-1 / (2 * Y 0)) := by
    fin_cases i
    · apply hc.1.trans (Real.exp_le_exp.mpr ?_)
      apply (le_div_iff₀ (by linarith only [hk] : 0 < 2 * Y 0)).mpr
      nlinarith only [sq_nonneg (Y 0 - 6), hk]
    · exact hc.2
  rw [hformula]
  exact ⟨mul_nonneg hi (hpos i).le, mul_pos_iff_of_pos_right (hpos i),
    (mul_le_mul_of_nonneg_left hbound hi).trans_eq (mul_comm _ _)⟩
