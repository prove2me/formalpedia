-- Prove2me | solution 2 for CohnElkies.saddleSmallRadiusPhase_pole_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:31.810211+00:00
-- url     : https://prove2.me/submissions/d62b3824-54c3-4ed0-8cdc-09c878db12bc

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    (ε ℓ : ℝ) (n : ℕ) :
    Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ)) =
      Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
        Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
        Real.exp
          (ℓ *
            (realHyperbolicShellPhase ε
              (1 + 2 * (n : ℝ) / ℓ) -
                realHyperbolicShellPhase ε 1) -
            2 * (n : ℝ) * saddleShellDerivativeOne ε) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

