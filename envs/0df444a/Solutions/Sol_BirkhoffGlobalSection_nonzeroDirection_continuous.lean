-- Prove2me | solution 1 for BirkhoffGlobalSection.nonzeroDirection_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:06.702998+00:00
-- url     : https://prove2.me/submissions/b71a9f6c-707a-47f0-810a-13db1ea2e741

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem solution : Continuous (fun y : ({x : Phase // x ≠ 0}) => (⟨normalize (y : Phase), norm_normalize y.property⟩ : ({x : Phase // ‖x‖ = 1}))) := by
  apply Continuous.subtype_mk
  change Continuous (fun y : ({x : Phase // x ≠ 0}) => ‖(y : Phase)‖⁻¹ • (y : Phase))
  exact (continuous_subtype_val.norm.inv₀
    (fun y => norm_ne_zero_iff.mpr y.property)).smul continuous_subtype_val
