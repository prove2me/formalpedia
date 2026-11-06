-- Prove2me | solution 1 for BianchiIX.gaussCode_map_le_of_cylinder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:02:24.776627+00:00
-- url     : https://prove2.me/submissions/5b7ed8ce-dcaa-4126-8591-bdd5f610cc48

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussCode_preimage_open_le
import Theorems.Thm_BianchiIX_measurable_gaussCode
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


/-- Prefix mass bounds imply domination for every measurable image set. -/
theorem solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [ν.OuterRegular] (a : X → ℕ → ℕ+)
    (ha : Measurable a)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ ν (gaussCylinder w)) :
    Measure.map (gaussCode ∘ a) μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply (measurable_gaussCode.comp ha) hs, s.measure_eq_iInf_isOpen ν]
  apply le_iInf
  intro O
  apply le_iInf
  intro hsO
  apply le_iInf
  intro hO
  exact (measure_mono (preimage_mono hsO)).trans (gaussCode_preimage_open_le μ ν a hbound hO)
