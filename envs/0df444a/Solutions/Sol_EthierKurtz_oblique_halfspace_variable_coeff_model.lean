-- Prove2me | solution 1 for EthierKurtz.oblique_halfspace_variable_coeff_model
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T22:31:26.346142+00:00
-- url     : https://prove2.me/submissions/afd88492-1770-4cda-98de-a80d902dae1a

import Mathlib
import Theorems.Thm_EthierKurtz_oblique_kernel_schauder_resolvent
import Theorems.Thm_EthierKurtz_oblique_halfspace_kernel_hypotheses
import Theorems.Thm_EthierKurtz_oblique_variable_coeff_perturbation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

theorem ball_sub_half {d : ℕ} {e x : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hx : 0 < inner ℝ x e) :
    Metric.ball x (inner ℝ x e) ⊆ {y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e} := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  show 0 ≤ inner ℝ y e
  have h1 : inner ℝ x e - inner ℝ y e = inner ℝ (x - y) e := (inner_sub_left _ _ _).symm
  have h2 : |inner ℝ (x - y) e| ≤ ‖x - y‖ * ‖e‖ := abs_real_inner_le_norm _ _
  rw [he, mul_one, norm_sub_rev] at h2
  have h3 := (abs_le.mp h2).2
  linarith

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ (d : ℕ) (μ : ℝ), 0 < μ → μ < 1 →
        ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
          ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
          ∀ (α : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (β : EuclideanSpace ℝ (Fin d) → Fin d → ℝ),
            (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
            (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
              ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
            (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
            (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
              ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
            ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |g y| ≤ M) →
            (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
            ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
              (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
              (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
                lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
                  - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
                  - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
              (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
              (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
                |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
                |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
                |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
              (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
                |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
                |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
                |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by
  intro d μ hμ0 hμ1
  refine EthierKurtz.oblique_variable_coeff_perturbation d μ hμ0 hμ1 ?_
  intro e b he hb
  obtain ⟨K, K1, K2, K3, A, c, hKH, hBC⟩ := EthierKurtz.oblique_halfspace_kernel_hypotheses d e b he hb
  obtain ⟨C, hC, hsol⟩ := EthierKurtz.oblique_kernel_schauder_resolvent d {y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e} K K1 K2 K3 A c μ hμ0 hμ1 hKH
  refine ⟨C, hC, fun lam hlam h hH hM => ?_⟩
  obtain ⟨Hh, hHh⟩ := hH
  obtain ⟨M0, hM0⟩ := hM
  obtain ⟨u, u1, u2, hd, heq, hbc, hb2⟩ :=
    hsol lam hlam h ⟨Hh, fun y hy z hz => hHh y z hy hz⟩ ⟨M0, fun y hy => hM0 y hy⟩
  refine ⟨u, u1, u2, fun x hx => hd x (inner ℝ x e) hx (ball_sub_half he hx), fun x hx => heq x hx,
    fun x hx => hbc x (b - e) (fun t ht y _ => hBC t ht x hx y), fun M0 Hh hM0 hHh hsup hhol => ?_⟩
  obtain ⟨h1, h2⟩ := hb2 M0 Hh hM0 hHh (fun y hy => hsup y hy) (fun y hy z hz => hhol y z hy hz)
  exact ⟨fun x hx v w => h1 x hx v w, fun x x' hx hx' v w => h2 x hx x' hx' v w⟩
