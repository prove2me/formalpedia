-- Prove2me | solution 1 for CohnElkies.saddleNegativeContour_sourceNormalizationFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/27d76944-7ec0-458d-81c8-8bed00cf8f52

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_halfIntegerFactor

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (ε ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ (2 * N + 1) *
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) *
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) /
      (Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hrad := saddleSmallRadiusVariable_halfIntegerFactor
    ε hr N
  have hden :
      Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) ≠ 0 := by
    positivity
  field_simp [hden]
  rw [show ℓ * Real.log Real.pi / 2 =
    (ℓ / 2) * Real.log Real.pi by ring]
  rw [show
    Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N *
        Real.exp (saddleNegativeContourPhaseError ε ℓ N) =
      (Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N) *
        (Real.exp ((ℓ / 2) * Real.log Real.pi) *
          Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N)) by ring]
  rw [← hrad]
  unfold saddleNegativeContourPhaseError saddleTaylorContour
  push_cast
  have hexponents :
      Real.exp
          ((ℓ - -(2 * (N : ℝ) + 1)) *
            Real.log Real.pi / 2) *
        Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (saddleNegativeContourOrdinate ℓ N)) =
      Real.exp
          ((2 * (N : ℝ) + 1) *
            (Real.log Real.pi / 2 +
              saddleShellDerivativeOne ε)) *
        (Real.exp ((ℓ / 2) * Real.log Real.pi) *
          Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
          Real.exp
            (ℓ *
              (realHyperbolicShellPhase ε
                (saddleNegativeContourOrdinate ℓ N) -
                  realHyperbolicShellPhase ε 1) -
              (2 * (N : ℝ) + 1) *
                saddleShellDerivativeOne ε)) := by
    rw [← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    r ^ (2 * N + 1) *
      Real.exp
        ((ℓ - -(2 * (N : ℝ) + 1)) *
          Real.log Real.pi / 2) *
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) =
      r ^ (2 * N + 1) *
        (Real.exp
          ((ℓ - -(2 * (N : ℝ) + 1)) *
            Real.log Real.pi / 2) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (saddleNegativeContourOrdinate ℓ N))) := by ring
    _ = r ^ (2 * N + 1) *
      (Real.exp
          ((2 * (N : ℝ) + 1) *
            (Real.log Real.pi / 2 +
              saddleShellDerivativeOne ε)) *
        (Real.exp ((ℓ / 2) * Real.log Real.pi) *
          Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
          Real.exp
            (ℓ *
              (realHyperbolicShellPhase ε
                (saddleNegativeContourOrdinate ℓ N) -
                  realHyperbolicShellPhase ε 1) -
              (2 * (N : ℝ) + 1) *
                saddleShellDerivativeOne ε))) := by
        rw [hexponents]
    _ = _ := by ring
end CohnElkies
