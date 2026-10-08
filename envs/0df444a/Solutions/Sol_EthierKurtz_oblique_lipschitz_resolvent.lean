-- Prove2me | solution 1 for EthierKurtz.oblique_lipschitz_resolvent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T03:07:04.222125+00:00
-- url     : https://prove2.me/submissions/b2ef36c6-5a1f-469d-bc33-1540fb4240e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EthierKurtz_oblique_holder_resolvent
import Theorems.Thm_EthierKurtz_lipschitz_holder_closure

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

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
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (K : NNReal),
      LipschitzWith K ⇑h →
        ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
          lam₀ • fg.1 - fg.2 = h := by
  obtain ⟨lam₀, hlam₀, hsolv⟩ := oblique_holder_resolvent n hd Ω
    hbounded hconnected hopen μ hμ hboundary a b c normal ha haHolder hbHolder
    helliptic hc hnormal hoblique
  refine ⟨lam₀, hlam₀, ?_⟩
  intro h K hLip
  obtain ⟨C, hHold⟩ := lipschitz_holder_closure n Ω hbounded μ hμ h K hLip
  obtain ⟨fg, hfg, hsol⟩ := hsolv h C hHold
  exact ⟨fg, subset_closure hfg, hsol⟩
