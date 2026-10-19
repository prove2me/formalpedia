-- Prove2me | solution 1 for CohnElkies.norm_plusPolynomial_negativeContour_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/c7f49f70-85ac-46e6-8d83-5f14928affb2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_one_le_saddleNegativeContourOrdinate
import Theorems.Thm_CohnElkies_saddleTaylorContour_shellArgument
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
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (s : ℝ) :
    ‖plusPolynomial ε
      (Complex.I *
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
            (ℓ : ℂ))‖ ≤
      27 * (1 + |beta ε|) * (1 + |s|) ^ 3 := by
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  have hκ : 1 ≤ κ :=
    one_le_saddleNegativeContourOrdinate hℓ N
  have hκtop : κ ≤ 2 :=
    saddleNegativeContourOrdinate_le_two hℓ N hN
  have hℓone : 1 ≤ ℓ := by
    norm_num [Nat.cast_add, Nat.cast_one] at hN
    have hcast : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hdivide : |s| / ℓ ≤ |s| :=
    (div_le_self (abs_nonneg s) hℓone)
  have hnorm :
      ‖((-s / ℓ : ℝ) : ℂ) +
        Complex.I * (((-κ : ℝ) : ℂ))‖ ≤
        |s| / ℓ + κ := by
    calc
      ‖((-s / ℓ : ℝ) : ℂ) +
        Complex.I * (((-κ : ℝ) : ℂ))‖ ≤
        ‖((-s / ℓ : ℝ) : ℂ)‖ +
          ‖Complex.I * (((-κ : ℝ) : ℂ))‖ :=
        norm_add_le _ _
      _ = |s| / ℓ + κ := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ,
          abs_of_nonneg (show 0 ≤ κ by linarith)]
  have hbase :
      1 + ‖((-s / ℓ : ℝ) : ℂ) +
        Complex.I * (((-κ : ℝ) : ℂ))‖ ≤
        3 * (1 + |s|) := by
    nlinarith [abs_nonneg s]
  rw [saddleTaylorContour_shellArgument hℓ N s]
  calc
    ‖plusPolynomial ε
        (((-s / ℓ : ℝ) : ℂ) +
          Complex.I * (((-κ : ℝ) : ℂ)))‖ ≤
      (1 + |beta ε|) *
        (1 + ‖((-s / ℓ : ℝ) : ℂ) +
          Complex.I * (((-κ : ℝ) : ℂ))‖) ^ 3 :=
      norm_plusPolynomial_le ε _
    _ ≤ (1 + |beta ε|) *
        (3 * (1 + |s|)) ^ 3 := by
      gcongr
    _ = 27 * (1 + |beta ε|) * (1 + |s|) ^ 3 := by
      ring
end CohnElkies
