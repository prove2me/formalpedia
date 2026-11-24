-- Prove2me | solution 1 for Formalism.UG.P.card_stabAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:18.346818+00:00
-- url     : https://prove2.me/submissions/09caad82-e0ff-463c-98f2-4f970a210f44

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep
import Theorems.Thm_Formalism_UG_P_mem_stabAt_mul_iff

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
theorem _root_.solution (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (stabAt Γ K ((γ : G) * g * κ)) = Nat.card (stabAt Γ K g) := by
  refine Nat.card_congr
    { toFun := fun δ => ⟨γ⁻¹ * δ.1 * γ, (mem_stabAt_mul_iff Γ K g γ κ δ.1).1 δ.2⟩
      invFun := fun δ => ⟨γ * δ.1 * γ⁻¹, (mem_stabAt_mul_iff Γ K g γ κ _).2 (by
        convert δ.2 using 2; group)⟩
      left_inv := fun δ => Subtype.ext (by group)
      right_inv := fun δ => Subtype.ext (by group) }
end Formalism.UG.P
