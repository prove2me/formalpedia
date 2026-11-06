-- Prove2me | solution 1 for BianchiIX.log_deriv_gaussWord_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:54:16.779218+00:00
-- url     : https://prove2.me/submissions/5b8e1e58-0ec0-42bc-ae04-07cad8a4761b

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Theorems.Thm_BianchiIX_abs_deriv_gaussWord_prefix
import Theorems.Thm_BianchiIX_digitPrefix_extendPositiveWord
import Theorems.Thm_BianchiIX_gaussPrefixLog_lipschitz
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

section
open BianchiIX
noncomputable section
open Set Finset

private theorem BianchiIX.log_abs_deriv_gaussWord_prefix (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.log |deriv (gaussWord (digitPrefix a n)) x| = gaussPrefixLog a n x := by
  rw [abs_deriv_gaussWord_prefix a n hx, one_div, Real.log_inv, Real.log_pow]
  simp [gaussPrefixLog]

end
end

open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX


theorem solution (w : List ℕ+) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.log (|deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) -
      Real.log (|deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) y|)| ≤ 2 * |x - y| := by
  rw [← digitPrefix_extendPositiveWord w,
    log_abs_deriv_gaussWord_prefix _ _ hx, log_abs_deriv_gaussWord_prefix _ _ hy]
  exact gaussPrefixLog_lipschitz _ _ hx hy
