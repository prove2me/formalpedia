-- Prove2me | solution 1 for ExpConMinimax.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:58:16.844553+00:00
-- url     : https://prove2.me/submissions/1659b341-3208-4ea3-b5f7-e1dce6616c1b

import Mathlib
import Definitions.Def_ExpConMinimax_Vec

open ExpConMinimax in
theorem solution {n m : ℕ} (X : Set (Vec n)) (f : Vec n → ℝ) (g : Vec n → Vec m)
    (xs : Vec n) (γs : Vec m) (hxs : xs ∈ X) (hγs : IsNonneg γs)
    (hsaddle : ∀ x ∈ X, ∀ γ : Vec m, IsNonneg γ →
      f xs + inner ℝ γ (g xs) ≤ f xs + inner ℝ γs (g xs) ∧
      f xs + inner ℝ γs (g xs) ≤ f x + inner ℝ γs (g x)) :
    ∀ x ∈ X, -(‖γs‖ * ‖vecPosPart (g x)‖) ≤ f x - f xs := by
  intro x hx
  have hz0 : IsNonneg (0 : Vec m) := fun i => by simp
  have h2n : IsNonneg ((2:ℝ) • γs) := fun i => by
    show 0 ≤ ((2:ℝ) • γs) i
    rw [PiLp.smul_apply, smul_eq_mul]
    nlinarith [hγs i]
  have h0 := (hsaddle x hx 0 hz0).1
  rw [inner_zero_left] at h0
  have h2 := (hsaddle x hx ((2:ℝ) • γs) h2n).1
  rw [real_inner_smul_left] at h2
  have hsec := (hsaddle x hx 0 hz0).2
  have hle : inner ℝ γs (g x) ≤ inner ℝ γs (vecPosPart (g x)) := by
    rw [← sub_nonneg, ← inner_sub_right, PiLp.inner_apply]
    apply Finset.sum_nonneg
    intro i _
    rw [PiLp.sub_apply, Real.inner_apply]
    apply mul_nonneg (hγs i)
    unfold vecPosPart
    rw [PiLp.toLp_apply]
    linarith [le_max_left (g x i) 0]
  have hcs := real_inner_le_norm γs (vecPosPart (g x))
  linarith
