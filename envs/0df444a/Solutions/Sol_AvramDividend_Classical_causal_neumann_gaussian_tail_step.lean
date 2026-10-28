-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_gaussian_tail_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:08:07.758144+00:00
-- url     : https://prove2.me/submissions/4d86bfd1-dae3-4019-a8cb-42eec126796f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_neumann_undamped_primitive_step

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The weighted Gaussian Neumann primitives inherit the exact Volterra tail recurrence. -/
theorem solution
    (a w β : ℝ) (K k : ℝ → ℝ) (P Q : ℕ → ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      Q (n + 2) x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * Q (n + 1) s ∂volume) := by
  intro n x hx
  let I : ℝ → ℝ := fun y =>
    ∫ t in Ioc (0 : ℝ) y, Real.exp (w * t) * P n t ∂volume
  have hQnext : Q (n + 1) = fun y : ℝ => (1 / a) * I y := hQsucc n
  have hQnext2 : Q (n + 2) x = (1 / a) *
      (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P (n + 1) t ∂volume) := by
    simpa only [Nat.add_assoc] using congrFun (hQsucc (n + 1)) x
  have hconv :
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * Q (n + 1) s ∂volume) =
      (1 / a) * (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * I s ∂volume) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) x,
          (1 / a) * ((β + K (x - s)) * I s) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun s => by
              change (β + K (x - s)) * Q (n + 1) s =
                (1 / a) * ((β + K (x - s)) * I s)
              rw [congrFun hQnext s]
              ring)
      _ = _ := integral_const_mul (1 / a) _
  rw [hQnext2]
  rw [causal_signed_neumann_undamped_primitive_step
    a w β K k P hk hkL1 hPL1 hPrec n x hx]
  rw [hconv]
  simp only [one_div]
  ring
