-- Prove2me | solution 1 for EthierKurtz.oblique_local_pieces_general_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T23:38:36.991024+00:00
-- url     : https://prove2.me/submissions/51749396-09ea-40ae-ae5b-a2957717ab78

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Theorems.Thm_EthierKurtz_oblique_interior_local_solver_general_coeff
import Theorems.Thm_EthierKurtz_oblique_boundary_chart_local_inverse
import Theorems.Thm_EthierKurtz_oblique_flattened_coefficient_bounds
import Theorems.Thm_EthierKurtz_oblique_boundary_local_solver_general_coeff
import Theorems.Thm_EthierKurtz_oblique_local_pieces_from_local_solvers

set_option autoImplicit false

open MeasureTheory Real Set Filter
open scoped Topology BoundedContinuousFunction

theorem solution (d : ℕ) (hd : 0 < d) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hV : ∀ A0 : Matrix (Fin d) (Fin d) ℝ, A0.PosDef →
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
        lam * u x - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
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
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA : (∀ x0 ∈ closure Ω, ∃ R Ka : ℝ, 0 < R ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
          ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)))
    (hpd : ∀ x ∈ closure Ω, (a x).PosDef)
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) ∧
        (∀ x ∈ Metric.ball x0 r0,
          (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)) ∧
        0 ≤ K ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖DΘ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖D2Θ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) :
    ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (χ1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (χ2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (lam0 C Ka : ℝ),
      (0 < ρ ∧
        0 < τ ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt χ (χ1 x) x ∧ HasFDerivAt χ1 (χ2 x) x) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, χ1 x (c x) = 0) ∧
        (∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → χ y = 0 ∧ χ1 y = 0 ∧ χ2 y = 0) ∧
        (∀ y ∈ Metric.ball x0 τ, χ y = 1) ∧
        (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
        0 ≤ Z ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ x - χ y‖ ≤ Z * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ1 x‖ ≤ Z) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ1 x - χ1 y‖ ≤ Z * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ2 x‖ ≤ Z) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ2 x - χ2 y‖ ≤ Z * ‖x - y‖ ^ μ)) ∧ 1 ≤ lam0 ∧ 0 ≤ C ∧
      (∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : EuclideanSpace ℝ (Fin d) → ℝ) (W1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (W2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - W1 x (bb x) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) ∧ 0 ≤ Ka ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) := by
  refine EthierKurtz.oblique_local_pieces_from_local_solvers d hd Ω hΩ μ hμ0 hμ1 c a bb ?_ ?_ hA hpd hch
  · intro x0 r0 K e b Θ DΘ D2Θ hchart Ka hab hah hpd0
    have hinv := EthierKurtz.oblique_boundary_chart_local_inverse d Ω μ hμ0 hμ1 c x0 r0 K e b Θ DΘ D2Θ hchart
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ := hchart
    have hx0S : x0 ∈ Metric.ball x0 r0 ∩ closure Ω :=
      ⟨Metric.mem_ball_self h1, frontier_subset_closure
        ((h8 x0 (Metric.mem_ball_self h1)).2.mpr (by rw [h6, inner_zero_left]))⟩
    exact EthierKurtz.oblique_boundary_local_solver_general_coeff d Ω μ hμ0 hμ1 c hV x0 r0 K e b Θ DΘ D2Θ
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ hinv a bb Ka hab hah
      (fun Z Λ ρ hΛS h0Z hΛ0 hΛl hρ => EthierKurtz.oblique_flattened_coefficient_bounds d
        (Metric.ball x0 r0 ∩ closure Ω) Z μ K ρ Ka Θ DΘ D2Θ ⟨k1, k2, k3, k4, k5, k6⟩ x0 hx0S h7 Λ hΛS h0Z hΛ0 hΛl hρ
        hμ0.le hμ1.le a bb hab hah) hpd0
  · intro x0 R hR hball Ka hab hah hpd0
    exact EthierKurtz.oblique_interior_local_solver_general_coeff d hd Ω hΩ μ hμ0 hμ1 c hV x0 R hR hball a bb Ka
      hab hah hpd0
