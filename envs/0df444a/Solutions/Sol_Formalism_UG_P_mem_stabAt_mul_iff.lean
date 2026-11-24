-- Prove2me | solution 1 for Formalism.UG.P.mem_stabAt_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:01.669737+00:00
-- url     : https://prove2.me/submissions/ea857111-9d76-4732-a937-6d3ec877297f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep

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
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by
  simp only [stabAt, Set.mem_setOf_eq]
  have e : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast; group
  rw [e, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]
end Formalism.UG.P
