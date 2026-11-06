-- Prove2me | solution 1 for BianchiIX.gaussPrefixLog_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:24:46.894014+00:00
-- url     : https://prove2.me/submissions/c9d60f9c-76bf-4795-abc9-dc256d5d5174

import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Theorems.Thm_BianchiIX_gaussDenoms_bounds
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

open BianchiIX
noncomputable section
open Set Finset

private theorem BianchiIX.gaussDenom_pos (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < gaussDenom a n x := by
  have h := gaussDenoms_bounds a n
  dsimp [gaussDenom]
  nlinarith [mul_nonneg h.2.1 hx]

theorem solution (a : ℕ → ℕ+) (n : ℕ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussPrefixLog a n x - gaussPrefixLog a n y| ≤ 2 * |x - y| := by
  have hd (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      HasDerivWithinAt (gaussPrefixLog a n)
        (-2 * ((gaussDenoms a n).2 / gaussDenom a n t)) (Ici 0) t := by
    have h := (((hasDerivAt_id t).const_mul (gaussDenoms a n).2).const_add
      (gaussDenoms a n).1).log (gaussDenom_pos a n ht).ne'
    convert! (h.const_mul (-2)).hasDerivWithinAt (s := Ici 0) using 1
    simp [gaussDenom]
  have hb (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      ‖-2 * ((gaussDenoms a n).2 / gaussDenom a n t)‖ ≤ (2 : ℝ) := by
    have h := gaussDenoms_bounds a n
    have hpos := gaussDenom_pos a n ht
    have hrat : (gaussDenoms a n).2 / gaussDenom a n t ≤ 1 := by
      apply (div_le_one hpos).mpr
      dsimp [gaussDenom]
      nlinarith [mul_nonneg h.2.1 ht]
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg h.2.1, abs_of_pos hpos]
    norm_num
    linarith
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx
