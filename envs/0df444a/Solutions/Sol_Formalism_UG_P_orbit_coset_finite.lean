-- Prove2me | solution 1 for Formalism.UG.P.orbit_coset_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:15.498321+00:00
-- url     : https://prove2.me/submissions/e38fdafc-1a36-43f2-a42a-5060db9d56f6

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Theorems.Thm_Formalism_UG_P_stabilizer_coset_eq

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
theorem _root_.solution (hK : IsCommensurated K) (s : G) :
    (MulAction.orbit K ((s : G ⧸ K))).Finite := by
  have h1 : ((K.map (MulAut.conj s).toMonoidHom).subgroupOf K).index ≠ 0 := hK s
  rw [← stabilizer_coset_eq] at h1
  haveI : Finite (K ⧸ MulAction.stabilizer K ((s : G ⧸ K))) := Nat.finite_of_card_ne_zero h1
  exact Set.finite_coe_iff.mp ((MulAction.orbitEquivQuotientStabilizer K _).finite_iff.mpr this)
end Formalism.UG.P
