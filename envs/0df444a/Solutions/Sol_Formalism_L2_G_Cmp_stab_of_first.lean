-- Prove2me | solution 1 for Formalism.L2.G.Cmp.stab_of_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:57.299007+00:00
-- url     : https://prove2.me/submissions/9e55b3e8-5dd6-4b7f-a8f4-ad0977368673

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsHypA
import Theorems.Thm_Formalism_L2_G_Cmp_map_of_first

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {T K : Type} [CommRing T] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
  (φ : T ≃+* K × K) (σ : T →+* T) (hσ : ∀ t, φ (σ t) = swapR K (φ t)) (Ov : Subring K) (S : Subring T)
  (hS : ∀ t, t ∈ S ↔ (φ t).1 ∈ Ov ∧ (φ t).2 ∈ Ov) (J : Matrix n n T) (Λ : Submodule S (n → T))
  (hΛ : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform σ J z y ∈ S)
include hσ hS hΛ
namespace Formalism.L2.G.Cmp
theorem _root_.solution (x : GL n T) (hx : x ∈ UJ σ J)
    (h1 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ (((x : Matrix n n T) *ᵥ y) a)).1)
    (h2 : ∀ y ∈ Λ, ∃ y' ∈ Λ, ∀ a, (φ (y' a)).1 = (φ ((((x⁻¹ : GL n T) : Matrix n n T) *ᵥ y) a)).1) :
    x ∈ stabGL Λ := by
  show ∀ y : n → T, y ∈ Λ ↔ (x : Matrix n n T) *ᵥ y ∈ Λ
  intro y
  constructor
  · exact map_of_first φ σ hσ Ov S hS J Λ hΛ x hx h1 h2 y
  · intro hxy
    have hxi : x⁻¹ ∈ UJ σ J := inv_mem hx
    have := map_of_first φ σ hσ Ov S hS J Λ hΛ x⁻¹ hxi h2 (by simpa using h1) _ hxy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end Formalism.L2.G.Cmp
