-- Prove2me | solution 1 for EthierKurtz.oblique_boundary_flattening_charts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T00:12:49.740843+00:00
-- url     : https://prove2.me/submissions/8cdf31b1-d953-4bcc-841a-926026a370a2

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Theorems.Thm_EthierKurtz_oblique_shear_extension
import Theorems.Thm_EthierKurtz_oblique_flattened_chart_core
import Theorems.Thm_EthierKurtz_oblique_chart_from_core

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hP : ∀ (M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (e : EuclideanSpace ℝ (Fin (n + 1))),
        (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
        (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
        ∃ (E : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (DE : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (D2E : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)),
          (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
          (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
          (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
          ∃ C, 0 ≤ C ∧ ∀ x x' : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
            ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hΩ : IsOpen Ω) (hboundary : EthierKurtz.BoundaryCTwiceHolder Ω μ)
    (c ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (ν x))
    (hobl : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * ν x i) :
    ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
            (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
            (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
            0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
            (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
            Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
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
              ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ) := by
  exact EthierKurtz.oblique_chart_from_core n μ hμ0 hμ1 (EthierKurtz.oblique_flattened_chart_core n μ hμ0 hμ1 (EthierKurtz.oblique_shear_extension n μ hμ0 hμ1 hP)) Ω hΩ hboundary c ν hc hnormal hobl
