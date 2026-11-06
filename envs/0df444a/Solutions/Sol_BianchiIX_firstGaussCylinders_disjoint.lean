-- Prove2me | solution 1 for BianchiIX.firstGaussCylinders_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:58:13.783072+00:00
-- url     : https://prove2.me/submissions/dbb2f69e-6076-483d-a6ef-c69bd4353a98

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussCylinder_comparable
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


theorem solution (O : Set ℝ) :
    (firstGaussCylinders O).PairwiseDisjoint gaussCylinder := by
  intro v hv w hw hne
  apply Set.disjoint_left.mpr
  intro x hxv hxw
  rcases gaussCylinder_comparable hv.1 hw.1 ⟨x, hxv, hxw⟩ with hp | hp
  · have hlt : v.length < w.length := lt_of_le_of_ne hp.length_le
      (fun heq => hne (hp.eq_of_length heq))
    exact hw.2.2.2 v hv.2.2.1 hp hlt hv.2.1
  · have hlt : w.length < v.length := lt_of_le_of_ne hp.length_le
      (fun heq => hne (hp.eq_of_length heq).symm)
    exact hv.2.2.2 w hw.2.2.1 hp hlt hw.2.1
