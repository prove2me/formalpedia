-- Prove2me | solution 1 for EthierKurtz.oblique_semigroup_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T13:50:22.970831+00:00
-- url     : https://prove2.me/submissions/3643b289-bd25-486a-a9cc-a4ca9f05f223
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EthierKurtz_oblique_resolvent_positive
import Theorems.Thm_EthierKurtz_oblique_semigroup_positive_of_resolvent

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of positivity: the maximum principle gives resolvent positivity
on the graph, and the exponential formula lifts it to the semigroup. -/
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ))
    (hT : IsStronglyContinuousContractionSemigroup T)
    (hgen : ∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
        (f, g) ∈ closure (obliqueDiffusionGraph Ω μ a b c)) :
    ∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x := by
  exact EthierKurtz.oblique_semigroup_positive_of_resolvent n hd Ω hbounded
    hconnected hopen μ hμ hboundary a b c normal ha haHolder hbHolder helliptic
    hc hnormal hoblique T hT hgen
    (EthierKurtz.oblique_resolvent_positive n hd Ω hbounded hconnected hopen μ
      hμ hboundary a b c normal ha haHolder hbHolder helliptic hc hnormal
      hoblique)
