-- Prove2me | solution 1 for EthierKurtz.oblique_holder_resolvent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T13:31:10.596298+00:00
-- url     : https://prove2.me/submissions/5acbdba1-846d-454e-a870-d7e7058b5b4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Theorems.Thm_EthierKurtz_oblique_schauder_apriori_estimate
import Theorems.Thm_EthierKurtz_oblique_existence_from_apriori_estimate

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of Hölder-data resolvent existence to the Schauder theory:
the a priori estimate feeds the method-of-continuity existence machine. -/
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
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ a b c,
          lam₀ • fg.1 - fg.2 = h :=
  oblique_existence_from_apriori_estimate n hd Ω hbounded hconnected hopen μ hμ
    hboundary a b c normal ha haHolder hbHolder helliptic hc hnormal hoblique
    (oblique_schauder_apriori_estimate n hd Ω hbounded hconnected hopen μ hμ
      hboundary a b c normal ha haHolder hbHolder helliptic hc hnormal hoblique)
