-- Prove2me | solution 1 for BianchiIX.exists_digitPrefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:39:18.116406+00:00
-- url     : https://prove2.me/submissions/5e25e36d-0a20-4508-b6c1-45a2d79c1488

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX


theorem solution (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    ∃ a : ℕ → ℕ+, digitPrefix a w.length = w := by
  let a : ℕ → ℕ+ := fun n => if h : n < w.length then
    ⟨w[n], hw _ (List.getElem_mem h)⟩ else 1
  refine ⟨a, ?_⟩
  apply List.ext_getElem
  · exact digitPrefix_length a w.length
  · intro i hi _
    simp only [digitPrefix, List.length_map, List.length_range] at hi
    simp [digitPrefix, a, hi]
