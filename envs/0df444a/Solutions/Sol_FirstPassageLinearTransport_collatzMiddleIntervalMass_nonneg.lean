-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzMiddleIntervalMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:55.210315+00:00
-- url     : https://prove2.me/submissions/aa4790fc-781d-42f1-8fad-ca3cefa6a301

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) (a : ℝ) :
    0 ≤ collatzMiddleIntervalMass n a := by
  unfold collatzMiddleIntervalMass
  exact Finset.sum_nonneg fun v _hv ↦
    mul_nonneg
      (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le v)
      (by
        classical
        unfold collatzMiddleIntervalIndicator
        split <;> norm_num)
end FirstPassageLinearTransport
