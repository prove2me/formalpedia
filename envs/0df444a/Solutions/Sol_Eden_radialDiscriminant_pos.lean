-- Prove2me | solution 1 for Eden.radialDiscriminant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:00.370574+00:00
-- url     : https://prove2.me/submissions/5078a346-822c-4b07-8683-9880b0dd8874

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 < radialDiscriminant t s := by
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_nonneg (sub_nonneg.mpr he) (sq_nonneg (s - 1))
  have hp := Real.exp_pos (-4 * t)
  dsimp [radialDiscriminant]
  linarith
end Eden
