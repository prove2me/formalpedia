-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_series_volterra_identity_of_initial_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:41:51.296249+00:00
-- url     : https://prove2.me/submissions/faa8a061-9a17-450e-8646-143e56fc848c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_head_step
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_tail_step
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_nonpositive_zero
import Theorems.Thm_AvramDividend_Classical_causal_neumann_head_tail_global_step
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_reflected_full_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_resolvent
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The signed Gaussian Neumann series is the exact derivative resolvent. -/
theorem solution
    (a w β ρ : ℝ) (K k : ℝ → ℝ)
    (P Q : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hP0 : P 0 = k)
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
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x) :
    ∀ x : ℝ, a * g x +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume) = 1 := by
  have hfirst : Q 1 = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * k t ∂volume) := by
    simpa only [zero_add, hP0] using hQsucc 0
  have hhead :=
    causal_neumann_gaussian_head_step a w β K k Q hk hQ0 hfirst
  have htail :=
    causal_neumann_gaussian_tail_step a w β K k P Q
      hk hkL1 hPL1 hPrec hQsucc
  have hzero :=
    causal_neumann_gaussian_nonpositive_zero a w P Q hQsucc
  have hstep :=
    causal_neumann_head_tail_global_step a
      (fun t : ℝ => β + K t) Q hhead htail hzero
  have hB : ∀ x : ℝ, IntegrableOn
      (fun s : ℝ => β + K (x - s)) (Ioc (0 : ℝ) x) volume := by
    intro x
    exact causal_gaussian_reflected_full_kernel_integrable K β x hK
  have hres := causal_geometric_neumann_resolvent
    a ρ (fun t : ℝ => β + K t) (fun _ : ℝ => 1 / a) g Q
    hρ0 hρ1 hQ0 hstep hB hMeas hGeom hPoint hg
  intro x
  have heq := hres x
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    a * g x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume) =
      a * (g x + (1 / a) * (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume)) := by
          field_simp [ha0]
    _ = a * (1 / a) := by rw [heq]
    _ = 1 := by field_simp [ha0]
