-- Prove2me | solution 1 for EthierKurtz.oblique_dense_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T04:51:11.913676+00:00
-- url     : https://prove2.me/submissions/0af2e0e2-6a1a-40d4-b494-7a6fdc9c7672
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EthierKurtz_oblique_lipschitz_resolvent
import Theorems.Thm_EthierKurtz_lipschitz_dense_closure

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of dense range: solve exactly on a Lipschitz approximant, then
transfer the estimate to the target by rewriting with the exact solution and
halving the tolerance. -/
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
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ A, ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by
  obtain ⟨lam₀, hlam₀, hsolv⟩ := EthierKurtz.oblique_lipschitz_resolvent n hd Ω
    hbounded hconnected hopen μ hμ hboundary a b c normal ha haHolder hbHolder
    helliptic hc hnormal hoblique
  refine ⟨lam₀, hlam₀, fun h delta hdelta => ?_⟩
  obtain ⟨h', ⟨K, hLip⟩, hclose⟩ := EthierKurtz.lipschitz_dense_closure n Ω
    hbounded h (delta / 2) (half_pos hdelta)
  obtain ⟨fg, hfg, hsol⟩ := hsolv h' K hLip
  exact ⟨fg, hfg, by
    rw [hsol]
    exact lt_of_lt_of_le hclose (half_le_self hdelta.le)⟩
