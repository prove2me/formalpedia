-- Prove2me | solution 1 for CohnElkies.upperNegativeHalfGamma_norm_eq_reflected_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/7e1fc307-2fc2-4b87-95a7-386b7d62c4d4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaShifted_modulus_eq_exp_neg_damping
import Theorems.Thm_CohnElkies_saddleNegativeGammaRate_pos
import Theorems.Thm_CohnElkies_upperNegativeHalfGamma_reflection_norm

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
      (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp
          (upperGammaDamping ℓ
            (saddleNegativeGammaRate ℓ N) (-s / ℓ)) /
          Real.cosh (Real.pi * (s / 2)) := by
  let η : ℝ := saddleNegativeGammaRate ℓ N
  let D : ℝ := upperGammaDamping ℓ η (-s / ℓ)
  let q : ℝ := (N : ℝ) + 3 / 2
  have hη : 0 < η := saddleNegativeGammaRate_pos hℓ N
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hΓ : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hmass : ℓ * η / 2 = q := by
    try dsimp [η, q, saddleNegativeGammaRate]
    field_simp [hℓ.ne']
  have hfreq : ℓ * (-s / ℓ) / 2 = -s / 2 := by
    field_simp [hℓ.ne']
  have hmod := upperGammaShifted_modulus_eq_exp_neg_damping
    hℓ hη (-s / ℓ)
  rw [hmass, hfreq] at hmod
  have harg :
      ((q : ℂ) - Complex.I * (((-s / 2 : ℝ) : ℂ))) =
        (q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg] at hmod
  have href := upperNegativeHalfGamma_reflection_norm N s
  change
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
      ‖Complex.Gamma
        ((q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)))‖ =
      Real.pi / Real.cosh (Real.pi * (s / 2)) at href
  rw [hmod] at href
  change
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
      (Real.pi / Real.Gamma q) * Real.exp D /
        Real.cosh (Real.pi * (s / 2))
  rw [Real.exp_neg] at href
  field_simp [hΓ.ne', (Real.exp_pos D).ne',
    (Real.cosh_pos (Real.pi * (s / 2))).ne'] at href ⊢
  simpa [D, neg_div, mul_comm, mul_left_comm, mul_assoc] using! href
end CohnElkies
