-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_series_volterra_identity
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:53:11.017427+00:00
-- url     : https://prove2.me/submissions/c468ecf6-f6a5-417a-a0eb-c66183ae9efb

import Mathlib
open MeasureTheory Set

theorem solution : ¬ (∀ (a w β ρ : ℝ) (K k : ℝ → ℝ)
    (P Q : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume))
    (hMeas : ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)))
    (hGeom : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x, ‖Q n s‖ ≤ C * ρ ^ n)
    (hPoint : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n)
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x),
    ∀ x : ℝ, a * g x +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume) = 1) := by
  intro h
  have hbound : ∀ n : ℕ, ∀ s : ℝ, ‖(if n = 0 then (1:ℝ) else 0)‖ ≤ 1 * (0:ℝ) ^ n := by
    intro n s; rcases n with _ | n <;> simp
  have H := h 1 1 1 0 (fun _ => 0)
    (fun t => if 0 < t then -((1:ℝ)⁻¹ * Real.exp (-1 * t) * (1 + (fun _ => (0:ℝ)) t)) else 0)
    (fun _ _ => 0) (fun n _ => if n = 0 then 1 else 0) (fun _ => 1)
    one_pos le_rfl one_pos integrableOn_zero rfl ?_ (fun _ => integrableOn_zero)
    (fun n => by funext x; simp) (by funext x; simp) (fun n => by funext x; simp)
    (fun _ _ => aestronglyMeasurable_const) (fun _ => ⟨1, zero_le_one, fun n s _ => hbound n s⟩)
    (fun _ => ⟨1, zero_le_one, fun n => hbound n 0⟩)
    (fun x => by simp [tsum_ite_eq]) 1
  · norm_num at H
  · have := (exp_neg_integrableOn_Ioi 0 one_pos).neg
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [show (0:ℝ) < t from ht]
