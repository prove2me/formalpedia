-- Prove2me | solution 1 for CohnElkies.exists_plusSaddleSmallRadiusPhase_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/09c9fef8-d551-4432-88ac-680761e21576

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_realHyperbolicShellPhase_quadratic_remainder

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
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
          |ℓ *
              (realHyperbolicShellPhase ε
                (1 + 2 * (n : ℝ) / ℓ) -
                  realHyperbolicShellPhase ε 1) -
              2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
            C * (n : ℝ) ^ 2 / ℓ := by
  obtain ⟨C, hCnonneg, hC⟩ :=
    exists_realHyperbolicShellPhase_quadratic_remainder
      hε horder
  refine ⟨4 * C, by positivity, ?_⟩
  intro ℓ hℓ n hn
  let x : ℝ := 1 + 2 * (n : ℝ) / ℓ
  have hratio : 0 ≤ 2 * (n : ℝ) / ℓ := by
    positivity
  have hratioupper : 2 * (n : ℝ) / ℓ ≤ 1 :=
    (div_le_iff₀ hℓ).mpr (by simpa using! hn)
  have hx : x ∈ Set.Icc (1 : ℝ) 2 := by
    constructor <;> dsimp [x] <;> linarith
  have hscale : ℓ * (x - 1) = 2 * (n : ℝ) := by
    try dsimp [x]
    field_simp; ring
  have hidentity :
      ℓ * (realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε =
      ℓ * (realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1 -
          (x - 1) * saddleShellDerivativeOne ε) := by
    rw [← hscale]
    ring
  change
    |ℓ * (realHyperbolicShellPhase ε x -
      realHyperbolicShellPhase ε 1) -
        2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
      (4 * C) * (n : ℝ) ^ 2 / ℓ
  calc
    |ℓ * (realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε| =
      ℓ * |realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1 -
          (x - 1) * saddleShellDerivativeOne ε| := by
        rw [hidentity, abs_mul, abs_of_pos hℓ]
    _ ≤ ℓ * (C * (x - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (hC x hx) hℓ.le
    _ = (4 * C) * (n : ℝ) ^ 2 / ℓ := by
      try dsimp [x]
      field_simp; ring
end CohnElkies
