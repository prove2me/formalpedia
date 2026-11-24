-- Prove2me | solution 1 for Formalism.UG.P.rho_eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:46.42824+00:00
-- url     : https://prove2.me/submissions/73561bfb-6bae-4b56-bb52-939ef0886919

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (Γ K : Subgroup G)
namespace Formalism.UG.P
theorem _root_.solution {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ W) (x : G) (w : W)
    (hw : ∀ γ ∈ stabAt Γ K x, ρ γ w = w) (γ γ' : Γ) (κ κ' : K)
    (e : (γ : G) * x * κ = (γ' : G) * x * κ') : ρ γ w = ρ γ' w := by
  have e' : (γ : G) = (γ' : G) * x * (κ' : G) * (κ : G)⁻¹ * x⁻¹ := by
    rw [← e]
    group
  have hmem : x⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * x ∈ K := by
    have h1 : x⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * x = (κ' : G) * (κ : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e']
      group
    rw [h1]
    exact K.mul_mem κ'.2 (K.inv_mem κ.2)
  have h := hw (γ'⁻¹ * γ) hmem
  calc ρ γ w = ρ (γ' * (γ'⁻¹ * γ)) w := by rw [mul_inv_cancel_left]
    _ = ρ γ' (ρ (γ'⁻¹ * γ) w) := by rw [map_mul]; rfl
    _ = ρ γ' w := by rw [h]
end Formalism.UG.P
