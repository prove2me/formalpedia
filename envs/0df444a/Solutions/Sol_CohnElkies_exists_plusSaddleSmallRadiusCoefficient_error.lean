-- Prove2me | solution 1 for CohnElkies.exists_plusSaddleSmallRadiusCoefficient_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/2d875e3d-3506-4c1e-b2ed-1c4407c62e7a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadiusPhase_error
import Theorems.Thm_CohnElkies_plusSaddleSmallRadiusCoefficient_error_of_phase

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
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
            (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
              Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
  obtain ⟨C, hC, hphase⟩ :=
    exists_plusSaddleSmallRadiusPhase_error hε horder
  let K : ℝ := 18 / beta ε
  have hK : 0 ≤ K := by
    try dsimp [K]
    positivity [beta_pos hε]
  refine ⟨C + K, add_nonneg hC hK, ?_⟩
  intro ℓ hℓ n hn
  have hsource := plusSaddleSmallRadiusCoefficient_error_of_phase
    hε hℓ n hn C hC (hphase ℓ hℓ n hn)
  have hnreal : 0 ≤ (n : ℝ) := by positivity
  have hpoly :
      C * (n : ℝ) ^ 2 / ℓ + K * ((n : ℝ) / ℓ) ≤
        (C + K) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
    rw [show C * (n : ℝ) ^ 2 / ℓ +
          K * ((n : ℝ) / ℓ) =
        (C * (n : ℝ) ^ 2 + K * (n : ℝ)) / ℓ by
          ring]
    apply (div_le_div_iff_of_pos_right hℓ).mpr
    nlinarith [mul_nonneg hC hnreal,
      mul_nonneg hK (sq_nonneg (n : ℝ))]
  have hq :
      C * (n : ℝ) ^ 2 / ℓ ≤
        (C + K) * (n : ℝ) ^ 2 / ℓ := by
    gcongr
    exact le_add_of_nonneg_right hK
  have hright :
      0 ≤ (C + K) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
    positivity
  calc
    |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
      (C * (n : ℝ) ^ 2 / ℓ +
        K * ((n : ℝ) / ℓ)) *
          Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
            simpa [K] using! hsource
    _ ≤ ((C + K) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
          Real.exp ((C + K) * (n : ℝ) ^ 2 / ℓ) :=
        mul_le_mul hpoly (Real.exp_le_exp.mpr hq)
          (Real.exp_pos _).le hright
end CohnElkies
