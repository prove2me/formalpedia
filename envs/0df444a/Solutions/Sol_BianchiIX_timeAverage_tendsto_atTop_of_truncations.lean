-- Prove2me | solution 1 for BianchiIX.timeAverage_tendsto_atTop_of_truncations
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:30:47.007372+00:00
-- url     : https://prove2.me/submissions/912cd64a-51bd-418f-9b8f-70d2ef9dd302

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Theorems.Thm_BianchiIX_timeAverage_mono
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor


open Set Filter
open scoped Topology
open BianchiIX


theorem solution {u l : ℕ → ℝ}
    (htrunc : ∀ R : ℕ, Tendsto (timeAverage (fun j => min (u j) (R : ℝ))) atTop (𝓝 (l R)))
    (hl : Tendsto l atTop atTop) : Tendsto (timeAverage u) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨R, hR⟩ := ((tendsto_atTop.mp hl) (b + 1)).exists
  have hb : b < l R := by linarith
  filter_upwards [(tendsto_order.mp (htrunc R)).1 b hb] with n hn
  exact hn.le.trans (timeAverage_mono (fun j => min_le_left (u j) (R : ℝ)) n)
