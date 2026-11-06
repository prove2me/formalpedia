-- Prove2me | solution 1 for BianchiIX.gaussCode_map_le_smul_of_cylinder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:03:31.829454+00:00
-- url     : https://prove2.me/submissions/dafcb1a7-a40a-4ae6-8cb3-d1a0cb30184f

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussCode_map_le_of_cylinder_bounds
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
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal


theorem solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [ν.OuterRegular] (a : X → ℕ → ℕ+)
    (ha : Measurable a) (C : ℝ≥0)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ (C : ℝ≥0∞) * ν (gaussCylinder w)) :
    Measure.map (gaussCode ∘ a) μ ≤ C • ν := by
  apply gaussCode_map_le_of_cylinder_bounds μ (C • ν) a ha
  intro w hwne hw
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using hbound w hwne hw
