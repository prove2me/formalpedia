-- Prove2me | solution 1 for EthierKurtz.oblique_base_from_halfspace_model
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T00:01:00.773985+00:00
-- url     : https://prove2.me/submissions/2ab87d1f-832c-456f-915d-5a9cd15050b9

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Theorems.Thm_EthierKurtz_oblique_halfspace_model_fails_lipschitz
import Theorems.Thm_EthierKurtz_oblique_base_from_halfspace_model_lt_one

open Filter
open scoped Topology BoundedContinuousFunction

open scoped BoundedContinuousFunction
open EthierKurtz in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (hModel : ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (h : (closure {x : EuclideanSpace ℝ (Fin (n + 1)) |
        (0 : ℝ) < x (0 : Fin (n + 1))}) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph
          {x : EuclideanSpace ℝ (Fin (n + 1)) |
            (0 : ℝ) < x (0 : Fin (n + 1))} μ (fun _ => 1) (fun _ => 0)
          (fun _ => EuclideanSpace.single (0 : Fin (n + 1)) (-1 : ℝ)),
          lam₀ • fg.1 - fg.2 = h) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h := by
  rcases hμ.2.lt_or_eq with hlt | heq1
  · exact EthierKurtz.oblique_base_from_halfspace_model_lt_one n hd Ω hbounded hconnected hopen μ hμ hlt hboundary c normal hc hnormal hoblique
  · subst heq1
    exact absurd hModel (EthierKurtz.oblique_halfspace_model_fails_lipschitz n hd)
