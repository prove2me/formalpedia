-- Prove2me | solution 1 for BianchiIX.normalizedMaxDomain_rebase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:17:47.742657+00:00
-- url     : https://prove2.me/submissions/c2a9512a-2bcd-495f-a674-1742bd9c84e1

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


theorem solution {x : NormalizedState} {t₀ s : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) :
    normalizedMaxDomain (normalizedMaxCurve x t₀ s) s = normalizedMaxDomain x t₀ := by
  let S := maximalNormalizedSolution x t₀
  have hsub := (S.rebase hs).domain_subset_maximal
  let T := maximalNormalizedSolution (S.curve s) s
  have ht₀ : t₀ ∈ T.domain := hsub S.initial_mem
  have hinit : T.curve t₀ = x :=
    (normalizedMaxCurve_eqOn (S.rebase hs) S.initial_mem).trans S.initial_eq
  let U : NormalizedSolution x t₀ :=
    ⟨T.domain, T.isOpen_domain, T.convex_domain, ht₀, T.curve, hinit, T.hasDerivAt⟩
  exact Subset.antisymm U.domain_subset_maximal hsub
