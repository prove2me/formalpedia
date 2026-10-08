-- Prove2me | solution 1 for EthierKurtz.oblique_laplacian_base_solvability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T20:04:32.08843+00:00
-- url     : https://prove2.me/submissions/e0fe51f1-0269-493c-9894-f3c65277ef2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Theorems.Thm_EthierKurtz_oblique_halfspace_model_solvability
import Theorems.Thm_EthierKurtz_oblique_base_from_halfspace_model

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz

/-- Reduction of base-case solvability to the half-space model: the
localization assembly applied to the model problem. -/
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h :=
  oblique_base_from_halfspace_model n hd Ω hbounded hconnected hopen μ hμ
    hboundary c normal hc hnormal hoblique
    (oblique_halfspace_model_solvability n hd μ hμ)
