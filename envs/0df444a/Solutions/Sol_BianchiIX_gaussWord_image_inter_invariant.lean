-- Prove2me | solution 1 for BianchiIX.gaussWord_image_inter_invariant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:44:50.098822+00:00
-- url     : https://prove2.me/submissions/bb36befe-631c-429e-8ddf-7a1621ed92f8

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussWord_mem_invariant
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


theorem solution {E : Set ℝ} (hE : gaussMap ⁻¹' E = E)
    (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) :
    gaussWord w '' (Ioo (0 : ℝ) 1 ∩ E) = gaussCylinder w ∩ E := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxE⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (gaussWord_mem_invariant hE w hw hx).mpr hxE⟩
  · rintro ⟨⟨x, hx, rfl⟩, hyE⟩
    exact ⟨x, ⟨hx, (gaussWord_mem_invariant hE w hw hx).mp hyE⟩, rfl⟩
