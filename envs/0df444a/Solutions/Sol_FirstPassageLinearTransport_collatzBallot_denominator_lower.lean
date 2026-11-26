-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzBallot_denominator_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:54.082867+00:00
-- url     : https://prove2.me/submissions/274345ee-9625-4e8e-b07d-d3b2a73e237f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzBallotOuterLength_lower
import Theorems.Thm_FirstPassageLinearTransport_collatzBallotMiddleLength_lower

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) * Real.sqrt m / 16 ≤
      Real.sqrt (collatzBallotOuterLength m) *
        Real.sqrt (collatzBallotOuterLength m) *
          Real.sqrt (collatzBallotMiddleLength m) := by
  have ha : (m : ℝ) / 8 ≤ collatzBallotOuterLength m :=
    collatzBallotOuterLength_lower hm
  have hb : (m : ℝ) / 4 ≤ collatzBallotMiddleLength m :=
    collatzBallotMiddleLength_lower hm
  have hsqrtb : Real.sqrt ((m : ℝ) / 4) ≤
      Real.sqrt (collatzBallotMiddleLength m) := Real.sqrt_le_sqrt hb
  have hsqrta :
      Real.sqrt (collatzBallotOuterLength m) *
          Real.sqrt (collatzBallotOuterLength m) =
        (collatzBallotOuterLength m : ℝ) := by
    rw [← sq]
    exact Real.sq_sqrt (by positivity)
  have hsqrt_four : Real.sqrt ((m : ℝ) / 4) = Real.sqrt m / 2 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ m)]
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs]
      norm_num
    rw [hs4]
  rw [hsqrt_four] at hsqrtb
  rw [hsqrta]
  have hprod := mul_le_mul ha hsqrtb (by positivity) (by positivity)
  nlinarith
end FirstPassageLinearTransport
