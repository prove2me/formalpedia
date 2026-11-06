-- Prove2me | solution 1 for BianchiIX.invariant_set_volume_zero_or_compl_zero
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:48:35.30019+00:00
-- url     : https://prove2.me/submissions/f587b278-f05a-454e-bf31-7e732d66cefd

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_invariant_set_volume_domination
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
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution {E : Set ℝ} (hE : MeasurableSet E)
    (hinv : gaussMap ⁻¹' E = E) :
    (volume.restrict (Ioo (0 : ℝ) 1)) E = 0 ∨
      (volume.restrict (Ioo (0 : ℝ) 1)) Eᶜ = 0 := by
  have h := Measure.le_iff'.mp (invariant_set_volume_domination hE hinv) Eᶜ
  have hempty : Eᶜ ∩ (Ioo (0 : ℝ) 1 ∩ E) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false]
    tauto
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hE.compl,
    Measure.restrict_apply hE.compl, hempty, measure_empty] at h
  have hz := mul_eq_zero.mp (le_antisymm h bot_le)
  rcases hz with hz | hz
  · left
    have hB : volume (Ioo (0 : ℝ) 1 ∩ E) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    simpa only [Measure.restrict_apply hE, inter_comm] using hB
  · right
    simpa only [Measure.restrict_apply hE.compl] using hz
