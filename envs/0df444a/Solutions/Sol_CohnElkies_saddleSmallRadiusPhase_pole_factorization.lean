-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusPhase_pole_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/6f196ea6-056c-4724-a0ec-19817cbebbcd

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
namespace CohnElkies
theorem _root_.solution
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
  let H : ℝ := saddleShellDerivativeOne ε
  let p : ℝ :=
    realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ)
  let p₀ : ℝ := realHyperbolicShellPhase ε 1
  have harg :
      ℓ * p =
        ℓ * p₀ + (n : ℝ) * (2 * H) +
          (ℓ * (p - p₀) - 2 * (n : ℝ) * H) := by
    ring
  change Real.exp (ℓ * p) =
    Real.exp (ℓ * p₀) * Real.exp (2 * H) ^ n *
      Real.exp (ℓ * (p - p₀) - 2 * (n : ℝ) * H)
  rw [harg, Real.exp_add, Real.exp_add,
    Real.exp_nat_mul]
end CohnElkies
