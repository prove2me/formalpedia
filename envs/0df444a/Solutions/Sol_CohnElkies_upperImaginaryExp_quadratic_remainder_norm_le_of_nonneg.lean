-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/afa64782-cfd1-40fd-aeb6-4bc712a2a0f8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_iteratedDeriv
import Theorems.Thm_CohnElkies_upperImaginaryExp_contDiff
import Theorems.Thm_CohnElkies_upperImaginaryExp_iteratedDerivWithin_Icc
import Theorems.Thm_CohnElkies_upperImaginaryExp_taylorWithinEval_two
import Theorems.Thm_CohnElkies_upperImaginaryExp_cubicIntegral_norm_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 0 ≤ x) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ) +
          ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      x ^ 3 / 6 := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp [upperImaginaryExp]
  have hcont :
      ContDiffOn ℝ (3 : ℕ)
        upperImaginaryExp (Set.uIcc 0 x) :=
    (upperImaginaryExp_contDiff.of_le
      (by simp : (3 : WithTop ℕ∞) ≤ ⊤)).contDiffOn
  have htaylor :=
    taylor_integral_remainder
      (f := upperImaginaryExp) (x := x)
      (x₀ := 0) (n := 2) hcont
  rw [Set.uIcc_of_le hx,
    upperImaginaryExp_taylorWithinEval_two hxpos]
    at htaylor
  have hremainder :
      upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) +
            ((x ^ 2 / 2 : ℝ) : ℂ) =
        ∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / 2 : ℝ) •
            iteratedDeriv 3 upperImaginaryExp t := by
    calc
      upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) +
            ((x ^ 2 / 2 : ℝ) : ℂ) =
          upperImaginaryExp x -
            (1 + Complex.I * (x : ℂ) -
              ((x ^ 2 / 2 : ℝ) : ℂ)) := by ring
      _ = ∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
            iteratedDerivWithin 3 upperImaginaryExp
              (Icc (0 : ℝ) x) t := htaylor
      _ = ∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / 2 : ℝ) •
            iteratedDeriv 3 upperImaginaryExp t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        change
          ((x - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
              iteratedDerivWithin 3 upperImaginaryExp
                (Icc (0 : ℝ) x) t =
            ((x - t) ^ 2 / 2 : ℝ) •
              iteratedDeriv 3 upperImaginaryExp t
        rw [upperImaginaryExp_iteratedDerivWithin_Icc
          hxpos ht 3,
          ← upperImaginaryExp_iteratedDeriv 3 t]
        norm_num
  rw [hremainder]
  exact upperImaginaryExp_cubicIntegral_norm_le hx
end CohnElkies
