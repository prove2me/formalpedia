-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreGrowthPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:34:32.62072+00:00
-- url     : https://prove2.me/submissions/fa777cc0-cb3d-499e-a2ca-6bf2f6bd72a7

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX


theorem solution (k z : ℝ) :
    HasDerivAt (coreGrowthPrimitive k) (2 / Real.cosh z + 24 * ((1 / 10000) / k)) z := by
  have H := (((Real.hasDerivAt_arctan (Real.sinh z)).comp z (Real.hasDerivAt_sinh z)).const_mul 2).add
    ((hasDerivAt_id z).const_mul (24 * ((1 / 10000) / k)))
  apply H.congr_deriv
  rw [← Real.cosh_sq']
  field_simp [ne_of_gt (Real.cosh_pos z)]
