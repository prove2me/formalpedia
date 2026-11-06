-- Prove2me | solution 1 for BianchiIX.exists_gauss_inverse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:38:50.966804+00:00
-- url     : https://prove2.me/submissions/7dbedbf0-0474-438e-9acb-842173bcb170

import Definitions.Def_BianchiIX_Statistics_GaussInverse
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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, gaussInv ((j : ℝ) + 1) (gaussMap x) = x := by
  have hinv : 0 < 1 / x := one_div_pos.mpr hx.1
  have hk : 1 ≤ ⌊1 / x⌋₊ := Nat.one_le_floor_iff _ |>.mpr
    ((le_div_iff₀ hx.1).mpr (by linarith [hx.2]))
  refine ⟨⌊1 / x⌋₊ - 1, ?_⟩
  have hcast : ((⌊1 / x⌋₊ - 1 : ℕ) : ℝ) + 1 = (⌊1 / x⌋ : ℤ) := by
    rw [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel,
      natCast_floor_eq_intCast_floor hinv.le]
  rw [gaussInv, hcast, gaussMap, Int.floor_add_fract, one_div_one_div]
