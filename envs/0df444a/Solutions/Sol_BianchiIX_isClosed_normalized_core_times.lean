-- Prove2me | solution 1 for BianchiIX.isClosed_normalized_core_times
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:41:14.184458+00:00
-- url     : https://prove2.me/submissions/dc754d84-5c8d-4ac4-90a3-dc2edc64bc48

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
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

private theorem BianchiIX.isClosed_coreRegion (k : ℝ) : IsClosed {y : ProjectiveState | coreRegion k y} := by
  have hE : Continuous (fun y : ProjectiveState => |coreEnergy (y 0) (y 2) - k ^ 2|) := by
    unfold coreEnergy
    fun_prop
  have hP : Continuous (fun y : ProjectiveState => y 2 * y 3) := (continuous_apply 2).mul (continuous_apply 3)
  exact (isClosed_le hE continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 2)).inter
      (((isClosed_le continuous_const (continuous_apply 1)).inter (isClosed_le (continuous_apply 1) continuous_const)).inter
        ((isClosed_le continuous_const hP).inter (isClosed_le hP continuous_const))))

theorem solution {x : NormalizedState} {t₀ s T k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) :
    IsClosed ({u | 3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
      coreRegion k (toProjectiveState (normalizedMaxCurve x t₀ u))} ∩ Icc s T) := by
  let a := fun u => 1 + normalizedMaxCurve x t₀ u 0
  let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
  let c := 3 / (2 * k ^ 2)
  have hc0 : 0 < c := by
    dsimp [c]
    have hk0 : 0 < k := by linarith
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
  have H := hβ.preimage_isClosed_of_isClosed hD (isClosed_coreRegion k)
  convert! H using 1
  ext u
  change (c ≤ a u ∧ coreRegion k (β u)) ∧ u ∈ Icc s T ↔
    (u ∈ Icc s T ∧ c ≤ a u) ∧ coreRegion k (β u)
  tauto
