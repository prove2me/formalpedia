-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_gaussian_head_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:19:23.340417+00:00
-- url     : https://prove2.me/submissions/a8559f80-ba23-43c0-bb8a-a873b02383cc

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_gaussian_initial_weighted_primitive
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The first Gaussian Neumann correction obeys the exact resolvent recurrence. -/
theorem solution
    (a w β : ℝ) (K k : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQ1 : Q 1 = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * k t ∂volume)) :
    ∀ x : ℝ, 0 < x →
      Q 1 x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * Q 0 s ∂volume) := by
  intro x hx
  have hflip :
      (∫ s in Ioc (0 : ℝ) x, β + K s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, β + K (x - s) ∂volume) := by
    simpa only [one_mul, mul_one] using
      (positive_Ioc_causal_convolution_comm_real
        (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => β + K t) x
        (le_of_lt hx)).symm
  have hconv :
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * Q 0 s ∂volume) =
      (1 / a) * (∫ s in Ioc (0 : ℝ) x,
        β + K (x - s) ∂volume) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) x,
          (1 / a) * (β + K (x - s)) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun s => by
              change (β + K (x - s)) * Q 0 s =
                (1 / a) * (β + K (x - s))
              rw [congrFun hQ0 s]
              ring)
      _ = _ := integral_const_mul (1 / a) _
  rw [congrFun hQ1 x]
  rw [causal_signed_gaussian_initial_weighted_primitive a w β K k hk x]
  rw [hflip, hconv]
  simp only [one_div]
  ring
