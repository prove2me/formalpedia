-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_envelope_volterra_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:56:40.048438+00:00
-- url     : https://prove2.me/submissions/e6a43e9f-a2f1-4ac1-90be-5f019e08dd1e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_primitive_geometric_witness
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_weighted_series_identification
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_primitive_local_geometric
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_nonpositive_zero
import Theorems.Thm_AvramDividend_Classical_causal_neumann_local_to_pointwise_geom
import Theorems.Thm_AvramDividend_Classical_causal_neumann_measurable_from_c1_primitives
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_summable
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_series_volterra_identity_of_initial_power
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Signed Gaussian envelope bounds establish the exact Volterra resolvent equation. -/
theorem solution
    (K k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (a β w ρ : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hP0 : P 0 = k)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1))
    (hg : g = fun y : ℝ => 1 / a + Real.exp (w * y) *
      (∑' n : ℕ, (Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y,
          Real.exp (w * s) * P n s ∂volume)) / a)) :
    ∀ x : ℝ, a * g x +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume) = 1 := by
  obtain ⟨H, hHdef, hHbound, hHcont⟩ :=
    causal_gaussian_primitive_geometric_witness
      P F a w ρ ha hw hρ0 hPL1 hFL1 hDom hFmass
  obtain ⟨Q, hQ0, hQstep, hQsucc, hgsum⟩ :=
    causal_gaussian_weighted_series_identification P H g a w hHdef hg
  have hGeom :=
    causal_gaussian_primitive_local_geometric H Q a w ρ
      ha hw hρ0 hQ0 hQstep hHbound
  have hZero :=
    causal_neumann_gaussian_nonpositive_zero a w P Q hQsucc
  have hPoint :=
    causal_neumann_local_to_pointwise_geom Q a ρ
      ha hρ0 hQ0 hZero hGeom
  have hMeas :=
    causal_neumann_measurable_from_c1_primitives
      H Q a w hQ0 hQstep hHcont
  have hSummable : ∀ x : ℝ, Summable (fun n : ℕ => Q n x) := by
    intro x
    exact causal_geometric_neumann_summable Q ρ x hρ0 hρ1 (hPoint x)
  have hgQ : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x := by
    intro x
    exact hgsum x (hSummable x)
  exact causal_gaussian_series_volterra_identity_of_initial_power
    a w β ρ K k P Q g ha hρ0 hρ1 hK hk
    hkL1 hPL1 hPrec hP0 hQ0 hQsucc hMeas hGeom hPoint hgQ
