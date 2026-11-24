-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.rpow_nine_tenths_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:59.057308+00:00
-- url     : https://prove2.me/submissions/d0377566-86ab-4da5-8ace-9be62c14662c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution (c₃ B Y : ℝ) (hc₃ : 0 < c₃) (hB : 0 < B) (hY : 0 < Y) (hl : 0 < Real.log Y)
    (h1 : 120 * Real.log B ≤ Real.log Y) (h2 : 40 * Real.log (40 / c₃) ≤ Real.log Y) :
    Y ^ (9 / 10 : ℝ) ≤ c₃ * 1 * B ^ (-6 : ℝ) * Y / Real.log Y := by
  rw [le_div_iff₀ hl, Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hB]
  set l := Real.log Y with hldef
  set b := Real.log B with hbdef
  have hYl : Y = Real.exp l := (Real.exp_log hY).symm
  have a1 : l ≤ 40 * Real.exp (l / 40) := by
    have := Real.add_one_le_exp (l / 40)
    linarith
  have a2 : 40 ≤ c₃ * Real.exp (l / 40) := by
    have : Real.exp (Real.log (40 / c₃)) ≤ Real.exp (l / 40) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_log (by positivity), div_le_iff₀ hc₃] at this
    linarith
  have hE : 0 < Real.exp (l / 40) := Real.exp_pos _
  have hE9 : 0 < Real.exp (l * (9 / 10)) := Real.exp_pos _
  calc Real.exp (l * (9 / 10)) * l ≤ Real.exp (l * (9 / 10)) * (40 * Real.exp (l / 40)) :=
        mul_le_mul_of_nonneg_left a1 hE9.le
    _ ≤ Real.exp (l * (9 / 10)) * ((c₃ * Real.exp (l / 40)) * Real.exp (l / 40)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a2 hE.le) hE9.le
    _ = c₃ * Real.exp (l * (9 / 10) + l / 40 + l / 40) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ c₃ * Real.exp (b * (-6) + l) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hc₃.le
    _ = c₃ * 1 * Real.exp (b * (-6)) * Y := by
        rw [Real.exp_add, ← hYl]; ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
