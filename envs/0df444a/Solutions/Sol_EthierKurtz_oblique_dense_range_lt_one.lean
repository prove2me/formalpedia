-- Prove2me | solution 1 for EthierKurtz.oblique_dense_range_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:52:08.038941+00:00
-- url     : https://prove2.me/submissions/c20a77d2-6c32-4a57-8f78-6fc132627fa8

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Theorems.Thm_EthierKurtz_oblique_halfspace_variable_coeff_model
import Theorems.Thm_EthierKurtz_oblique_c2mu_extension_package
import Theorems.Thm_EthierKurtz_oblique_boundary_flattening_charts
import Theorems.Thm_EthierKurtz_oblique_halfspace_model_general_principal_part
import Theorems.Thm_EthierKurtz_oblique_local_pieces_general_coeff
import Theorems.Thm_EthierKurtz_oblique_global_solver_general_coeff_from_pieces
import Theorems.Thm_EthierKurtz_oblique_coefficient_extension_to_closure
import Theorems.Thm_EthierKurtz_oblique_density_from_global_solution

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction

open EthierKurtz in
set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ < 1)
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
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by
  have hV0 := EthierKurtz.oblique_halfspace_variable_coeff_model (n + 1) μ hμ.1 hμ.2
  have hVA := EthierKurtz.oblique_halfspace_model_general_principal_part (n + 1) μ hμ.1.le hV0
  have hP := EthierKurtz.oblique_c2mu_extension_package (n + 1) μ hμ.1 hμ.2
  have hch := EthierKurtz.oblique_boundary_flattening_charts n μ hμ.1 hμ.2 hP Ω hopen hboundary c normal hc
    hnormal hoblique
  obtain ⟨abar, bbar, heq, hA, hpd⟩ := EthierKurtz.oblique_coefficient_extension_to_closure (n + 1) Ω hopen μ hμ.1
    c hch a b haHolder hbHolder ha helliptic
  have hpiece := EthierKurtz.oblique_local_pieces_general_coeff (n + 1) (Nat.succ_pos n) Ω hopen μ hμ.1 hμ.2 c hVA
    abar bbar hA hpd hch
  have hG := EthierKurtz.oblique_global_solver_general_coeff_from_pieces (n + 1) Ω hopen hbounded μ hμ.1 hμ.2 c
    abar bbar hpiece
  exact EthierKurtz.oblique_density_from_global_solution (n + 1) Ω hopen hbounded μ hμ.1 hμ.2.le c a abar b bbar
    hG heq
