-- Prove2me | solution 1 for CohnElkies.upperNegativeContour_reflectedGamma_damping_exp_le_cosh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/582959f6-d28e-4a71-8129-a4834ae7a9a1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaShifted_modulus_eq_exp_neg_damping
import Theorems.Thm_CohnElkies_upperPositiveHalfGamma_scaled_sq_le
import Theorems.Thm_CohnElkies_saddleNegativeGammaRate_pos

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
    Real.exp
        (2 * upperGammaDamping ℓ
          (saddleNegativeGammaRate ℓ N) (-s / ℓ)) ≤
      Real.cosh (Real.pi * (s / 2)) := by
  let η : ℝ := saddleNegativeGammaRate ℓ N
  let D : ℝ := upperGammaDamping ℓ η (-s / ℓ)
  let q : ℝ := (N : ℝ) + 3 / 2
  have hη : 0 < η := saddleNegativeGammaRate_pos hℓ N
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hΓ : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hmod :
      ‖Complex.Gamma
        ((q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)))‖ =
        Real.Gamma q * Real.exp (-D) := by
    have h := upperGammaShifted_modulus_eq_exp_neg_damping
      hℓ hη (-s / ℓ)
    have hmass : ℓ * η / 2 = q := by
      try dsimp [η, q, saddleNegativeGammaRate]
      field_simp [hℓ.ne']
    have hfreq : ℓ * (-s / ℓ) / 2 = -s / 2 := by
      field_simp [hℓ.ne']
    rw [hmass, hfreq] at h
    have harg :
        ((q : ℂ) - Complex.I * (((-s / 2 : ℝ) : ℂ))) =
          (q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [harg] at h
    exact h
  have hhalf := upperPositiveHalfGamma_scaled_sq_le
    (N + 1) (s / 2)
  have hhalfnormal :
      Real.Gamma q ^ 2 ≤
        ‖Complex.Gamma
          ((q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)))‖ ^ 2 *
            Real.cosh (Real.pi * (s / 2)) := by
    have hcast : ((N + 1 : ℕ) : ℝ) + 1 / 2 = q := by
      try dsimp [q]
      norm_num [Nat.cast_add, Nat.cast_one]; ring
    rw [hcast] at hhalf
    exact hhalf
  rw [hmod, mul_pow] at hhalfnormal
  have hcancel :
      1 ≤ Real.exp (-D) ^ 2 *
        Real.cosh (Real.pi * (s / 2)) := by
    have hscaled :
        Real.Gamma q ^ 2 * 1 ≤
          Real.Gamma q ^ 2 *
            (Real.exp (-D) ^ 2 *
              Real.cosh (Real.pi * (s / 2))) := by
      simpa [mul_assoc] using! hhalfnormal
    exact le_of_mul_le_mul_left hscaled
      (sq_pos_of_pos hΓ)
  have hinverse :
      Real.exp (2 * D) * Real.exp (-D) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert! Real.exp_zero using 1; ring_nf
  change Real.exp (2 * D) ≤ Real.cosh (Real.pi * (s / 2))
  calc
    Real.exp (2 * D) = Real.exp (2 * D) * 1 := by ring
    _ ≤ Real.exp (2 * D) *
        (Real.exp (-D) ^ 2 *
          Real.cosh (Real.pi * (s / 2))) :=
      mul_le_mul_of_nonneg_left hcancel (Real.exp_pos _).le
    _ = Real.cosh (Real.pi * (s / 2)) := by
      rw [show Real.exp (2 * D) *
        (Real.exp (-D) ^ 2 * Real.cosh (Real.pi * (s / 2))) =
        (Real.exp (2 * D) * Real.exp (-D) ^ 2) *
          Real.cosh (Real.pi * (s / 2)) by ring,
        hinverse, one_mul]
end CohnElkies
