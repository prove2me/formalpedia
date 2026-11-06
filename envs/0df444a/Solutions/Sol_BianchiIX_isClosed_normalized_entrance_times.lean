-- Prove2me | solution 1 for BianchiIX.isClosed_normalized_entrance_times
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:57:41.331534+00:00
-- url     : https://prove2.me/submissions/55f4894c-52ac-4077-9433-c6ebda9db004

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
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
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.isClosed_entranceRegion (k : ℝ) : IsClosed {y : ProjectiveState | entranceRegion k y} := by
  have hR : Continuous (fun y : ProjectiveState => |coreRadius (y 0) (y 2) - k|) := by
    unfold coreRadius coreEnergy
    fun_prop
  exact (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le hR continuous_const).inter
      (((isClosed_le continuous_const (continuous_apply 1)).inter (isClosed_le (continuous_apply 1) continuous_const)).inter
        (((isClosed_le continuous_const (continuous_apply 2)).inter (isClosed_le (continuous_apply 2) continuous_const)).inter
          ((isClosed_le continuous_const (continuous_apply 3)).inter (isClosed_le (continuous_apply 3) continuous_const)))))

end
end

theorem solution {x : NormalizedState} {t₀ s T k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) :
    IsClosed ({r | 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧
      entranceRegion k (toProjectiveState (normalizedMaxCurve x t₀ r))} ∩ Icc s T) := by
  let a := normalizedProjectiveRate x t₀
  let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
  let c := 1 / (2 * (k + 1) ^ 2)
  have hK : 0 < k + 1 := by linarith
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hα (r : ℝ) (hr : r ∈ Icc s T) : ContinuousAt (normalizedMaxCurve x t₀) r :=
    (normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)).1.continuousAt
  have ha : ContinuousOn a (Icc s T) := fun r hr =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα r hr))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {r | c ≤ a r}) :=
    ha.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hY : ContinuousOn Y (Icc s T ∩ {r | c ≤ a r}) := by
    intro r hr
    exact ((contDiffAt_toProjectiveState 1 (hc0.trans_le hr.2).ne').continuousAt.comp (hα r hr.1)).continuousWithinAt
  have H := hY.preimage_isClosed_of_isClosed hD (isClosed_entranceRegion k)
  convert! H using 1
  ext r
  change (c ≤ a r ∧ entranceRegion k (Y r)) ∧ r ∈ Icc s T ↔
    (r ∈ Icc s T ∧ c ≤ a r) ∧ entranceRegion k (Y r)
  tauto
