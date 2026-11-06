-- Prove2me | solution 1 for BianchiIX.isClosed_normalized_connection_times
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:53:55.896954+00:00
-- url     : https://prove2.me/submissions/ab9e8bc0-c298-4cc1-8a88-2772bd1474e7

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
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
import Mathlib.Topology.Instances.Real.Lemmas
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
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.isClosed_connectionRegion (μ : ℝ) : IsClosed {y : ProjectiveState | connectionRegion μ y} := by
  have hm : Continuous (fun y : ProjectiveState => |-y 0 - μ|) := by fun_prop
  exact (isClosed_le hm continuous_const).inter
    (((isClosed_le continuous_const (continuous_apply 1)).inter (isClosed_le (continuous_apply 1) continuous_const)).inter
      (((isClosed_le continuous_const (continuous_apply 2)).inter (isClosed_le (continuous_apply 2) continuous_const)).inter
        ((isClosed_le continuous_const (continuous_apply 3)).inter (isClosed_le (continuous_apply 3) continuous_const))))

end
end

theorem solution {x : NormalizedState} {t₀ s T μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) :
    IsClosed ({u | 3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
      connectionRegion μ (toProjectiveState (normalizedMaxCurve x t₀ u))} ∩ Icc s T) := by
  let a := fun u => 1 + normalizedMaxCurve x t₀ u 0
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  let c := 3 / (2 * μ ^ 2)
  have hc0 : 0 < c := by
    dsimp [c]
    have hμ0 : 0 < μ := by linarith only [hμ]
    positivity
  have hα (u : ℝ) (hu : u ∈ Icc s T) : ContinuousAt (normalizedMaxCurve x t₀) u :=
    (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).1.continuousAt
  have ha : ContinuousOn a (Icc s T) := fun u hu =>
    (continuousAt_const.add ((continuous_apply 0).continuousAt.comp (hα u hu))).continuousWithinAt
  have hD : IsClosed (Icc s T ∩ {u | c ≤ a u}) :=
    ha.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hβ : ContinuousOn β (Icc s T ∩ {u | c ≤ a u}) := by
    intro u hu
    have hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0 := hc0.trans_le hu.2
    exact ((contDiffAt_toProjectiveState 1 (ne_of_gt hAu)).continuousAt.comp (hα u hu.1)).continuousWithinAt
  have H := hβ.preimage_isClosed_of_isClosed hD (isClosed_connectionRegion μ)
  convert! H using 1
  ext u
  change (c ≤ a u ∧ connectionRegion μ (β u)) ∧ u ∈ Icc s T ↔
    (u ∈ Icc s T ∧ c ≤ a u) ∧ connectionRegion μ (β u)
  tauto
