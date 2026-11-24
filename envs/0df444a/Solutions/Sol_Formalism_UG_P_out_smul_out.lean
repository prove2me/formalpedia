-- Prove2me | solution 1 for Formalism.UG.P.out_smul_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:29.815662+00:00
-- url     : https://prove2.me/submissions/4299341b-104c-42b3-87d2-bbf286ae6ba4

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc

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
variable {G : Type} [Group G] (K : Subgroup G)
namespace Formalism.UG.P
theorem _root_.solution (h : G) (z : G ⧸ K) : ∃ c : K, (h • z : G ⧸ K).out = h * z.out * c := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (h * z.out)
  refine ⟨c, ?_⟩
  have e : (h • z : G ⧸ K) = ((h * z.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  rw [e, hc]
end Formalism.UG.P
