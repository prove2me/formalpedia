-- Prove2me | solution 1 for CohnElkies.exists_saddleNegativeContourPhaseError_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/6a32801f-56ec-4ea8-b2f6-2a7a4212ab0e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_realHyperbolicShellPhase_quadratic_remainder
import Theorems.Thm_CohnElkies_one_le_saddleNegativeContourOrdinate
import Theorems.Thm_CohnElkies_saddleNegativeContourOrdinate_le_two

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
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ,
          2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ →
            |saddleNegativeContourPhaseError ε ℓ N| ≤
              K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
  obtain ⟨K, hK, hTaylor⟩ :=
    exists_realHyperbolicShellPhase_quadratic_remainder
      hε horder
  refine ⟨K, hK, ?_⟩
  intro ℓ hℓ N hN
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  have hκlow : 1 ≤ κ :=
    one_le_saddleNegativeContourOrdinate hℓ N
  have hκhigh : κ ≤ 2 :=
    saddleNegativeContourOrdinate_le_two hℓ N hN
  have hκmem : κ ∈ Icc (1 : ℝ) 2 :=
    ⟨hκlow, hκhigh⟩
  have ht := hTaylor κ hκmem
  have hscale :
      ℓ * (κ - 1) = 2 * (N : ℝ) + 1 := by
    try dsimp [κ, saddleNegativeContourOrdinate]
    field_simp [hℓ.ne']; ring
  have hidentity :
      saddleNegativeContourPhaseError ε ℓ N =
        ℓ *
          (realHyperbolicShellPhase ε κ -
            realHyperbolicShellPhase ε 1 -
              (κ - 1) * saddleShellDerivativeOne ε) := by
    unfold saddleNegativeContourPhaseError
    push_cast
    change
      ℓ * (realHyperbolicShellPhase ε κ -
        realHyperbolicShellPhase ε 1) -
          (2 * (N : ℝ) + 1) * saddleShellDerivativeOne ε = _
    rw [← hscale]
    ring
  rw [hidentity, abs_mul, abs_of_pos hℓ]
  calc
    ℓ *
      |realHyperbolicShellPhase ε κ -
        realHyperbolicShellPhase ε 1 -
          (κ - 1) * saddleShellDerivativeOne ε| ≤
      ℓ * (K * (κ - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left ht hℓ.le
    _ = K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
      rw [← hscale]
      field_simp [hℓ.ne']
end CohnElkies
