-- Prove2me | solution 1 for BirkhoffGlobalSection.radialDirectionMap_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:05.012348+00:00
-- url     : https://prove2.me/submissions/acb43e7a-fcfe-401b-a9af-3e699bd26223

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

theorem solution (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0) :
    Continuous ((fun s : S => (⟨normalize (s : Phase), norm_normalize (hsne s s.property)⟩ : ({x : Phase // ‖x‖ = 1})))) := by
  apply Continuous.subtype_mk
  change Continuous (fun s : S => ‖(s : Phase)‖⁻¹ • (s : Phase))
  exact (continuous_subtype_val.norm.inv₀
    (fun s => norm_ne_zero_iff.mpr (hsne s s.property))).smul continuous_subtype_val
