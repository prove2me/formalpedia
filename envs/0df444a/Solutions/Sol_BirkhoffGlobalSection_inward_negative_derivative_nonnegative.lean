-- Prove2me | solution 1 for BirkhoffGlobalSection.inward_negative_derivative_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:09.265275+00:00
-- url     : https://prove2.me/submissions/14fb8464-bfbc-45e9-a3f4-cad246e6ce95

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

theorem solution (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → f t < 0) : 0 ≤ d := by
  have hmax : IsMaxOn f (Set.Icc (0 : ℝ) 1) 1 := by
    intro t ht
    change f t ≤ f 1
    rcases ht.2.eq_or_lt with he | hlt
    · rw [he]
    · rw [hzero]
      exact (hneg t ht.1 hlt).le
  have hseg : segment ℝ (1 : ℝ) 0 ⊆ Set.Icc 0 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  have htangent := sub_mem_posTangentConeAt_of_segment_subset hseg
  have h := hmax.localize.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  simpa using h
