-- Prove2me | solution 1 for BubeckCO.PSGD.psgd_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:32:19.664373+00:00
-- url     : https://prove2.me/submissions/a19aaee0-a41b-4799-af9e-3824b253d2f8

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj
import Definitions.Def_BubeckCO_PSGD_IsPSGDRun
import Theorems.Thm_BubeckCO_PSGD_psgd_one_step
import Theorems.Thm_BubeckCO_PSGD_proj_inner_nonpos_and_pythag
set_option autoImplicit false

open BubeckCO.PSGD

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcompact : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R L η : ℝ) (hη : 0 < η)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) (ht : 1 ≤ t)
    (hR : ∀ z ∈ X, ‖z - x 1‖ ≤ R)
    (hL : ∀ s ∈ Finset.Icc 1 t, ‖g s‖ ≤ L)
    (hrun : IsPSGDRun X f η x g t)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤ R ^ 2 / (2 * η) + η * L ^ 2 * t / 2 := by
  have h_step : ∀ s ∈ Finset.Icc 1 t,
      f (x s) - f xstar ≤
        1 / (2 * η) * (‖x s - xstar‖ ^ 2 - ‖x (s + 1) - xstar‖ ^ 2) + η / 2 * L ^ 2 := by
    intro s hs
    rcases Finset.mem_Icc.mp hs with ⟨hs1, hst⟩
    rcases hrun s hs1 hst with ⟨hgs, hproj⟩
    have h1 := psgd_one_step X f η hη (x s) (g s) (x s - η • g s) xstar hgs rfl hxstar
    have h2 := (proj_inner_nonpos_and_pythag X hXcompact hXconv xstar hxstar
      (x s - η • g s) (x (s + 1)) hproj).2
    have h_f_le : f (x s) - f xstar ≤
        1 / (2 * η) * (‖x s - xstar‖ ^ 2 - ‖(x s - η • g s) - xstar‖ ^ 2) + η / 2 * ‖g s‖ ^ 2 := by
      linarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
    have h_norm_next : ‖x (s + 1) - xstar‖ ^ 2 ≤ ‖(x s - η • g s) - xstar‖ ^ 2 := by
      linarith [sq_nonneg ‖(x s - η • g s) - x (s + 1)‖]
    have h_div_pos : 0 ≤ 1 / (2 * η) := by positivity
    have h_term1 : 1 / (2 * η) * (‖x s - xstar‖ ^ 2 - ‖(x s - η • g s) - xstar‖ ^ 2) ≤
        1 / (2 * η) * (‖x s - xstar‖ ^ 2 - ‖x (s + 1) - xstar‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) h_div_pos
    have h_gs_sq : ‖g s‖ ^ 2 ≤ L ^ 2 := by
      nlinarith [norm_nonneg (g s), hL s hs]
    have h_term2 : η / 2 * ‖g s‖ ^ 2 ≤ η / 2 * L ^ 2 := by
      exact mul_le_mul_of_nonneg_left h_gs_sq (by positivity)
    linarith
  have h_sum_le := Finset.sum_le_sum h_step
  have h_sum_tel : ∀ k : ℕ, 1 ≤ k →
      ∑ s ∈ Finset.Icc 1 k,
        (1 / (2 * η) * (‖x s - xstar‖ ^ 2 - ‖x (s + 1) - xstar‖ ^ 2) + η / 2 * L ^ 2) =
      1 / (2 * η) * (‖x 1 - xstar‖ ^ 2 - ‖x (k + 1) - xstar‖ ^ 2) + (k : ℝ) * (η / 2 * L ^ 2) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  rw [h_sum_tel t ht] at h_sum_le
  have h_x1_sq : ‖x 1 - xstar‖ ^ 2 ≤ R ^ 2 := by
    rw [norm_sub_rev (x 1) xstar]
    nlinarith [norm_nonneg (xstar - x 1), hR xstar hxstar]
  have h_div_pos : 0 ≤ 1 / (2 * η) := by positivity
  have h_first_le : 1 / (2 * η) * (‖x 1 - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2) ≤
      R ^ 2 / (2 * η) := by
    have h_sub_le : ‖x 1 - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2 ≤ R ^ 2 := by
      linarith [sq_nonneg ‖x (t + 1) - xstar‖]
    calc 1 / (2 * η) * (‖x 1 - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2)
        ≤ 1 / (2 * η) * R ^ 2 := mul_le_mul_of_nonneg_left h_sub_le h_div_pos
      _ = R ^ 2 / (2 * η) := by ring
  linarith
