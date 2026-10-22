-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_coordinates_strict_inside_is_interior
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:07.338765+00:00
-- url     : https://prove2.me/submissions/c0fe547f-9380-486d-90f5-3f4a04d305e0

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

theorem solution (S : Set Phase)
    (τ : ({x : Phase // x ≠ 0}) → ℝ) (hτ : Continuous τ)
    (hK : ∀ y : ({x : Phase // x ≠ 0}), (y : Phase) ∈
      {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} ↔ τ y ≤ 1)
    (x : ({x : Phase // x ≠ 0})) (hx : τ x < 1) :
    (x : Phase) ∈ interior {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} := by
  let V : Set ({x : Phase // x ≠ 0}) := {y | τ y < 1}
  have hV : IsOpen V := isOpen_Iio.preimage hτ
  have hnonzero : IsOpen {y : Phase | y ≠ 0} := isOpen_ne
  have hU : IsOpen (Subtype.val '' V : Set Phase) :=
    hnonzero.isOpenEmbedding_subtypeVal.isOpenMap V hV
  have hxU : (x : Phase) ∈ (Subtype.val '' V : Set Phase) := ⟨x, hx, rfl⟩
  have hsub : (Subtype.val '' V : Set Phase) ⊆
      {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} := by
    rintro y ⟨z, hz, rfl⟩
    exact (hK z).mpr hz.le
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hU.mem_nhds hxU) hsub
