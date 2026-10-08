-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:48:14.824063+00:00
-- url     : https://prove2.me/submissions/bee58a64-1978-4506-9e4b-f2623e604f92

import Theorems.Thm_ConvexOptAlg_SmoothGD_thm_3_3_recursion
import Theorems.Thm_ConvexOptAlg_SmoothGD_thm_3_3_sequence_rate

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGDRun g (1 / β) x) (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * ‖x 1 - xstar‖ ^ 2 / ((t : ℝ) - 1) := by
  let C := 2 * β * ‖x 1 - xstar‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htime : 0 < (t : ℝ) - 1 := by
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hr (s : ℕ) (hs : 1 ≤ s) := thm_3_3_recursion f g β hβ hconv hf xstar hmin x hrun s hs
  change f (x t) - f xstar ≤ C / ((t : ℝ) - 1)
  by_cases hz : C = 0
  · have hh := hr t (by omega)
    change (f (x t) - f xstar) ^ 2 ≤ C * _ at hh
    rw [hz, zero_mul] at hh
    rw [hz, zero_div]
    nlinarith
  · have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hz)
    have hrec (s : ℕ) (hs : 1 ≤ s) :
        (1 / C) * (f (x s) - f xstar) ^ 2 + (f (x (s + 1)) - f xstar) ≤
          f (x s) - f xstar := by
      have hh := hr s hs
      change (f (x s) - f xstar) ^ 2 ≤ C * _ at hh
      have hdiv : (f (x s) - f xstar) ^ 2 / C ≤
          (f (x s) - f xstar) - (f (x (s + 1)) - f xstar) :=
        (div_le_iff₀ hCp).2 (by simpa [mul_comm] using hh)
      have hdiv' : (1 / C) * (f (x s) - f xstar) ^ 2 ≤
          (f (x s) - f xstar) - (f (x (s + 1)) - f xstar) := by
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      linarith
    have hh := thm_3_3_sequence_rate (fun s => f (x s) - f xstar) (1 / C)
      (one_div_pos.mpr hCp) (fun s _ => sub_nonneg.mpr (hmin (x s))) hrec t ht
    apply (le_div_iff₀ htime).2
    have hmul := mul_le_mul_of_nonneg_left hh hC
    have he : C * (1 / C * ((t : ℝ) - 1) * (f (x t) - f xstar)) =
        (f (x t) - f xstar) * ((t : ℝ) - 1) := by field_simp
    rw [he, mul_one] at hmul
    exact hmul
