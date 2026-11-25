-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.expSumLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:09.449613+00:00
-- url     : https://prove2.me/submissions/8b9f6b8a-c732-4608-b72c-89a8339a6737

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ExpSumLe := by
  intro x hx
  have hE : Real.exp (-x / 6) * Real.exp (x / 6) = 1 := by
    rw [← Real.exp_add, show -x / 6 + x / 6 = (0:ℝ) by ring, Real.exp_zero]
  have h3 : 3 ≤ Real.exp (x / 6) := by linarith [Real.add_one_le_exp (x / 6)]
  have hpos := Real.exp_pos (-x / 6)
  have hA : Real.exp (-x / 6) ≤ 1 / 3 := by nlinarith
  have hsplit : Real.exp (-x / 2) = Real.exp (-x / 3) * Real.exp (-x / 6) := by
    rw [← Real.exp_add]; congr 1; ring
  have t1 : Real.exp (-4 * x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have t2 : Real.exp (-x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp3 := Real.exp_pos (-x / 3)
  have hm := mul_le_mul_of_nonneg_left hA hp3.le
  linarith
end Formalism.HermitianLatticeCounting.P
