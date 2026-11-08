-- Prove2me | solution 1 for EllipsoidFitting.claim_4_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:53:43.660806+00:00
-- url     : https://prove2.me/submissions/d6284ffd-be87-4a05-b956-09d868051cf6

import Mathlib
import Definitions.Def_EllipsoidFitting_mpCoeff

set_option autoImplicit false

open EllipsoidFitting in
theorem solution (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (k t : ℕ) :
    |mpCoeff γ k t| ≤ γ ^ (-(t : ℝ) / 2) * (2 * Real.sqrt γ) ^ k := by
  have hs0 : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  have f3 : γ ≤ Real.sqrt γ := by
    have hs1 : Real.sqrt γ ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hγ1
    have hsq := Real.sq_sqrt hγ0.le
    nlinarith [Real.sqrt_nonneg γ]
  have f1 : ∀ t : ℕ, γ ^ (-((t + 2 : ℕ) : ℝ) / 2) * γ = γ ^ (-(t : ℝ) / 2) := by
    intro t
    have : -(t : ℝ) / 2 = -((t + 2 : ℕ) : ℝ) / 2 + 1 := by push_cast; ring
    rw [this, Real.rpow_add hγ0, Real.rpow_one]
  have f2 : ∀ t : ℕ, γ ^ (-((t + 1 : ℕ) : ℝ) / 2) * Real.sqrt γ = γ ^ (-(t : ℝ) / 2) := by
    intro t
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hγ0]
    congr 1
    push_cast
    ring
  have f4 : γ ^ (-((1 : ℕ) : ℝ) / 2) * γ = Real.sqrt γ := by
    rw [Real.sqrt_eq_rpow]
    have : (1 / 2 : ℝ) = -((1 : ℕ) : ℝ) / 2 + 1 := by push_cast; ring
    rw [this, Real.rpow_add hγ0, Real.rpow_one]
  have gpos : ∀ t : ℕ, 0 ≤ γ ^ (-(t : ℝ) / 2) := fun t => Real.rpow_nonneg hγ0.le _
  induction k generalizing t with
  | zero =>
    cases t with
    | zero => simp [mpCoeff]
    | succ t =>
      have h0 : mpCoeff γ 0 (t + 1) = 0 := by simp [mpCoeff]
      rw [h0, abs_zero]
      exact mul_nonneg (gpos _) (by positivity)
  | succ k ih =>
    have hP : 0 ≤ (2 * Real.sqrt γ) ^ k := by positivity
    cases t with
    | zero =>
      have e : mpCoeff γ (k + 1) 0 = γ * mpCoeff γ k 1 - γ * mpCoeff γ k 0 := by
        simp only [mpCoeff]
      rw [e]
      have a1 := ih 1
      have a0 := ih 0
      have g0 : γ ^ (-((0 : ℕ) : ℝ) / 2) = 1 := by simp
      rw [g0] at a0 ⊢
      have tri : |γ * mpCoeff γ k 1 - γ * mpCoeff γ k 0| ≤
          γ * |mpCoeff γ k 1| + γ * |mpCoeff γ k 0| := by
        have := abs_add_le (γ * mpCoeff γ k 1) (-(γ * mpCoeff γ k 0))
        rw [abs_neg, ← sub_eq_add_neg, abs_mul, abs_mul, abs_of_pos hγ0] at this
        exact this
      have b1 : γ * |mpCoeff γ k 1| ≤ Real.sqrt γ * (2 * Real.sqrt γ) ^ k := by
        calc γ * |mpCoeff γ k 1|
            ≤ γ * (γ ^ (-((1 : ℕ) : ℝ) / 2) * (2 * Real.sqrt γ) ^ k) :=
              mul_le_mul_of_nonneg_left a1 hγ0.le
          _ = (γ ^ (-((1 : ℕ) : ℝ) / 2) * γ) * (2 * Real.sqrt γ) ^ k := by ring
          _ = Real.sqrt γ * (2 * Real.sqrt γ) ^ k := by rw [f4]
      have b0 : γ * |mpCoeff γ k 0| ≤ Real.sqrt γ * (2 * Real.sqrt γ) ^ k := by
        calc γ * |mpCoeff γ k 0| ≤ γ * (1 * (2 * Real.sqrt γ) ^ k) :=
              mul_le_mul_of_nonneg_left a0 hγ0.le
          _ = γ * (2 * Real.sqrt γ) ^ k := by ring
          _ ≤ Real.sqrt γ * (2 * Real.sqrt γ) ^ k := mul_le_mul_of_nonneg_right f3 hP
      rw [pow_succ]
      nlinarith
    | succ t =>
      have e : mpCoeff γ (k + 1) (t + 1) = mpCoeff γ k t + γ * mpCoeff γ k (t + 2) := by
        simp only [mpCoeff]
      rw [e]
      have a1 := ih t
      have a2 := ih (t + 2)
      have tri : |mpCoeff γ k t + γ * mpCoeff γ k (t + 2)| ≤
          |mpCoeff γ k t| + γ * |mpCoeff γ k (t + 2)| := by
        have := abs_add_le (mpCoeff γ k t) (γ * mpCoeff γ k (t + 2))
        rw [abs_mul, abs_of_pos hγ0] at this
        exact this
      have b2 : γ * |mpCoeff γ k (t + 2)| ≤ γ ^ (-(t : ℝ) / 2) * (2 * Real.sqrt γ) ^ k := by
        calc γ * |mpCoeff γ k (t + 2)|
            ≤ γ * (γ ^ (-((t + 2 : ℕ) : ℝ) / 2) * (2 * Real.sqrt γ) ^ k) :=
              mul_le_mul_of_nonneg_left a2 hγ0.le
          _ = (γ ^ (-((t + 2 : ℕ) : ℝ) / 2) * γ) * (2 * Real.sqrt γ) ^ k := by ring
          _ = γ ^ (-(t : ℝ) / 2) * (2 * Real.sqrt γ) ^ k := by rw [f1]
      have rhs : γ ^ (-((t + 1 : ℕ) : ℝ) / 2) * (2 * Real.sqrt γ) ^ (k + 1) =
          2 * (γ ^ (-(t : ℝ) / 2) * (2 * Real.sqrt γ) ^ k) := by
        rw [← f2 t, pow_succ]
        ring
      rw [rhs]
      linarith
