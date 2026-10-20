-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:50:28.719646+00:00
-- url     : https://prove2.me/submissions/9440d551-a296-417b-aac2-e8da6db9bbdf

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

open CoopetSourcing.WholesalePrice

theorem solution (t wA wI : ℝ) (hwI : wI ≠ (3703 - 4066 * t - 242 * wA) / 9204) :
    CoopetSourcing.WholesalePrice.profitPool t wA wI <
      CoopetSourcing.WholesalePrice.profitPool t wA ((3703 - 4066 * t - 242 * wA) / 9204) := by
  have key : ∀ w : ℝ, profitPool t wA ((3703 - 4066 * t - 242 * wA) / 9204) - profitPool t wA w
      = (4066 * t + 242 * wA + 9204 * w - 3703) ^ 2 / 127677888 := by
    intro w
    simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI]
    ring
  have hne : 4066 * t + 242 * wA + 9204 * wI - 3703 ≠ 0 := by
    intro h; apply hwI; field_simp; linarith
  have hpos : 0 < (4066 * t + 242 * wA + 9204 * wI - 3703) ^ 2 := by positivity
  have := key wI
  nlinarith
