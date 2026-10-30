-- Prove2me | solution 1 for DerivativeChainContinuation.near_collision_local_mass
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:39:07.761464+00:00
-- url     : https://prove2.me/submissions/15158528-682f-4233-baec-d9681ff0f82b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_NearCollision
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (x : ι → ℂ) (c : ι → ℝ) (r a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (ha : 0 ≤ a)
    (hmass : ∀ i, a ≤ ∑ j, if ‖x i-x j‖ ≤ r then w j else 0) :
    a*((∑ i, w i*c i)-2*r) ≤ nearCollisionCharge w x c := by
  classical
  have hp (i : ι) : a*(c i-2*r) ≤ ∑ j, w j*max (c i-2*‖x i-x j‖) 0 := by
    calc
      _ ≤ a*max (c i-2*r) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
      _ ≤ (∑ j, if ‖x i-x j‖ ≤ r then w j else 0)*max (c i-2*r) 0 :=
        mul_le_mul_of_nonneg_right (hmass i) (le_max_right _ _)
      _ ≤ _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j _
        split_ifs with h
        · apply mul_le_mul_of_nonneg_left _ (hw j)
          exact max_le_max (by linarith) le_rfl
        · simpa using mul_nonneg (hw j) (le_max_right (c i-2*‖x i-x j‖) 0)
  have hh := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hp i) (hw i)
  have he : (∑ i, w i*(a*(c i-2*r)))=a*((∑ i, w i*c i)-2*r) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [mul_left_comm (w _) a]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]
  rw [he] at hh
  simpa only [nearCollisionCharge, Finset.mul_sum, mul_assoc] using hh
