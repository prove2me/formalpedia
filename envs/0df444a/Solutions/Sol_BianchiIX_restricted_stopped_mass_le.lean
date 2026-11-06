-- Prove2me | solution 1 for BianchiIX.restricted_stopped_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:59:12.240892+00:00
-- url     : https://prove2.me/submissions/8f2329af-bb90-453d-8222-34cf1182d24d

import Definitions.Def_BianchiIX_Statistics_StoppedMass
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

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal


theorem solution {I F : Set ℝ} {B : ℝ≥0∞} (hF : volume F ≤ B) :
    volume (I ∩ F) ≤ min (volume I) B :=
  le_min (measure_mono inter_subset_left) ((measure_mono inter_subset_right).trans hF)
