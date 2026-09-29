-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.saddle_point_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T15:43:27.354049+00:00
-- url     : https://prove2.me/submissions/ca6f6a7f-5135-449e-b0a4-d0c74a1e1bab

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_lagrangian

set_option autoImplicit false

open FirstOrderOpt.ConvexTheory in
theorem solution {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (lamStar : Fin m → ℝ) (yStar : Fin p → ℝ) (hlamStar : ∀ i, 0 ≤ lamStar i)
    (hsaddle1 : ∀ x ∈ X, lagrangian f g h xstar lamStar yStar ≤ lagrangian f g h x lamStar yStar)
    (hsaddle2 : ∀ lam : Fin m → ℝ, ∀ y : Fin p → ℝ, (∀ i, 0 ≤ lam i) →
        lagrangian f g h xstar lam y ≤ lagrangian f g h xstar lamStar yStar) :
    (∀ i, g i xstar ≤ 0) ∧ (∀ j, h j xstar = 0) ∧
      ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have H := hsaddle2 (lamStar + Pi.single i 1) yStar (by
      intro k
      simp only [Pi.add_apply]
      have := hlamStar k
      have : (0:ℝ) ≤ Pi.single (M := fun _ => ℝ) i 1 k := by
        rcases eq_or_ne k i with rfl | hk
        · simp
        · simp [Pi.single_apply, hk]
      linarith)
    unfold lagrangian at H
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at H
    linarith
  · intro j
    have H := hsaddle2 lamStar (yStar + Pi.single j (h j xstar)) hlamStar
    unfold lagrangian at H
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at H
    have : h j xstar * h j xstar ≤ 0 := by linarith
    nlinarith [mul_self_nonneg (h j xstar)]
  · intro x hx hg hh
    have H1 := hsaddle2 0 0 (fun _ => le_refl 0)
    have H2 := hsaddle1 x hx
    unfold lagrangian at H1 H2
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, hh, mul_zero] at H1 H2
    have : ∑ i, lamStar i * g i x ≤ 0 :=
      Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlamStar i) (hg i))
    linarith
