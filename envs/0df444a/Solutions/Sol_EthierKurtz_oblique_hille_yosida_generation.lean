-- Prove2me | solution 1 for EthierKurtz.oblique_hille_yosida_generation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T12:56:29.632309+00:00
-- url     : https://prove2.me/submissions/0df2b363-4e4f-49ba-a6f7-edd77e8f14c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EthierKurtz_oblique_hy_semigroup
import Theorems.Thm_EthierKurtz_oblique_semigroup_positive_conservative

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of the Hille-Yosida step: build the semigroup with exact
generator from the resolvent estimates, then equip it with positivity and
conservativeness from the maximum principle. -/
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
    (hest : ∀ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
      ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ,
      0 < delta → ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta) :
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∃ T : ℝ → ((closure Ω) →ᵇ ℝ) →L[ℝ] ((closure Ω) →ᵇ ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by
  obtain ⟨T, hT, hgen⟩ := EthierKurtz.oblique_hy_semigroup n hd Ω hbounded
    hconnected hopen μ hμ hboundary a b c normal ha haHolder hbHolder helliptic
    hc hnormal hoblique hest hrange
  obtain ⟨hpos, hcons⟩ := EthierKurtz.oblique_semigroup_positive_conservative
    n hd Ω hbounded hconnected hopen μ hμ hboundary a b c normal ha haHolder
    hbHolder helliptic hc hnormal hoblique T hT hgen
  exact ⟨T, hT, hpos, hcons, hgen⟩
