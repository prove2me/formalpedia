-- Prove2me | solution 1 for EthierKurtz.oblique_reflection_diffusion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T02:18:21.799074+00:00
-- url     : https://prove2.me/submissions/597416f8-f848-46bc-b9db-052a4a04d482
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EthierKurtz_oblique_closure_singlevalued
import Theorems.Thm_EthierKurtz_oblique_semigroup_generation

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of Theorem 1.5 to its two halves: single-valuedness of the
closed graph, and generation of the conservative positive contraction
semigroup with exact generator identification. -/
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
      ε ≤ ∑ i, c x i * normal x i) :
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by
  exact ⟨EthierKurtz.oblique_closure_singlevalued n hd Ω hbounded hconnected
      hopen μ hμ hboundary a b c normal ha haHolder hbHolder helliptic hc
      hnormal hoblique,
    EthierKurtz.oblique_semigroup_generation n hd Ω hbounded hconnected hopen
      μ hμ hboundary a b c normal ha haHolder hbHolder helliptic hc hnormal
      hoblique⟩
