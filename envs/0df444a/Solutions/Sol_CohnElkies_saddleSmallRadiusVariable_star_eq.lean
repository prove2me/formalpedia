-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusVariable_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/b3592f52-34d5-4b90-a296-7b22f05a4d65

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleLogRadius_eq_digamma_add_shellDerivative
import Theorems.Thm_CohnElkies_saddleSmallRadiusStar_gammaArgument

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} {d : ℕ} (hd : 0 < d) :
    saddleSmallRadiusVariable ε (saddleSmallRadiusStar ε d) =
      Real.exp
        (saddleDigamma
            (Real.log ((d : ℝ) / 2) / 8) +
          2 *
            (saddleShellDerivativeOne ε +
              saddleSourceShellDerivative ε
                (saddleSmallRadiusStarOrdinate ε d))) := by
  have hpi : Real.pi = Real.exp (Real.log Real.pi) :=
    (Real.exp_log Real.pi_pos).symm
  unfold saddleSmallRadiusVariable saddleSmallRadiusStar
  rw [saddleLogRadius_eq_digamma_add_shellDerivative,
    saddleSmallRadiusStar_gammaArgument hd ε]
  nth_rw 1 [hpi]
  rw [show (Real.exp
      (-(Real.log Real.pi) / 2 +
        saddleDigamma (Real.log ((d : ℝ) / 2) / 8) / 2 +
        saddleSourceShellDerivative ε
          (saddleSmallRadiusStarOrdinate ε d))) ^ 2 =
      Real.exp
        (2 * (-(Real.log Real.pi) / 2 +
          saddleDigamma (Real.log ((d : ℝ) / 2) / 8) / 2 +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d))) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
end CohnElkies
