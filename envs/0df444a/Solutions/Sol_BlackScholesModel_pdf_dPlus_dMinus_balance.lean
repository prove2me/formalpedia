-- Prove2me | solution 1 for BlackScholesModel.pdf_dPlus_dMinus_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T13:59:41.150989+00:00
-- url     : https://prove2.me/submissions/e32982e6-3704-4062-8c38-1cb3ad3a5986

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (S K r σ τ : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    S * stdNormalPDF (dPlus S K r σ τ) =
      K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ) := by
  have hroot : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hsqrt : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt (le_of_lt hτ)
  have hden : σ * Real.sqrt τ ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) (ne_of_gt hroot)
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hscale :
      dPlus S K r σ τ * (σ * Real.sqrt τ) =
        Real.log (S / K) + (r + σ ^ 2 / 2) * τ := by
    unfold dPlus
    field_simp [hden]
  have hshift :
      -(dMinus S K r σ τ) ^ 2 / 2 +
        (dPlus S K r σ τ) ^ 2 / 2 =
          Real.log (S / K) + r * τ := by
    calc
      _ = dPlus S K r σ τ * (σ * Real.sqrt τ) -
          σ ^ 2 * (Real.sqrt τ) ^ 2 / 2 := by
            unfold dMinus
            ring
      _ = Real.log (S / K) + r * τ := by
            rw [hsqrt]
            nlinarith [hscale]
  have hpdfshift :
      Real.exp (-(dMinus S K r σ τ) ^ 2 / 2) =
        (S / K) * Real.exp (r * τ) *
          Real.exp (-(dPlus S K r σ τ) ^ 2 / 2) := by
    have harg :
        -(dMinus S K r σ τ) ^ 2 / 2 =
          Real.log (S / K) + r * τ -
            (dPlus S K r σ τ) ^ 2 / 2 := by
      linarith [hshift]
    rw [harg, sub_eq_add_neg, Real.exp_add, Real.exp_add,
      Real.exp_log (div_pos hS hK)]
    simp only [neg_div]
    try ring
  have hecancel : Real.exp (-r * τ) * Real.exp (r * τ) = 1 := by
    rw [← Real.exp_add]
    have hzero : -r * τ + r * τ = 0 := by ring
    simp [hzero]
  have hKcancel : K * (S / K) = S := by
    field_simp [hK0]
  unfold stdNormalPDF
  rw [hpdfshift]
  calc
    S * ((1 / Real.sqrt (2 * Real.pi)) *
      Real.exp (-(dPlus S K r σ τ) ^ 2 / 2)) =
      (K * (S / K)) * ((1 / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(dPlus S K r σ τ) ^ 2 / 2)) := by rw [hKcancel]
    _ = (K * (S / K)) * ((1 / Real.sqrt (2 * Real.pi)) *
      Real.exp (-(dPlus S K r σ τ) ^ 2 / 2)) *
        (Real.exp (-r * τ) * Real.exp (r * τ)) := by
          rw [hecancel]
          ring
    _ = K * Real.exp (-r * τ) *
      ((1 / Real.sqrt (2 * Real.pi)) *
        ((S / K) * Real.exp (r * τ) *
          Real.exp (-(dPlus S K r σ τ) ^ 2 / 2))) := by ring