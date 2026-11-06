-- Prove2me | solution 1 for BianchiIX.mem_normalizedMaxDomain_retime
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:17:45.280601+00:00
-- url     : https://prove2.me/submissions/fa53473e-2f65-4772-be69-0163800fb7d0

import Definitions.Def_BianchiIX_Dynamics_FlowComposition
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

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


theorem solution {x : NormalizedState} {t₀ t₁ t : ℝ} :
    t ∈ normalizedMaxDomain x t₁ ↔ t + t₀ - t₁ ∈ normalizedMaxDomain x t₀ := by
  constructor
  · intro ht
    apply ((maximalNormalizedSolution x t₁).retime t₀).domain_subset_maximal
    change (t + t₀ - t₁) + t₁ - t₀ ∈ normalizedMaxDomain x t₁
    convert! ht using 1
    ring
  · intro ht
    exact ((maximalNormalizedSolution x t₀).retime t₁).domain_subset_maximal ht
