-- Prove2me | solution 1 for Formalism.UG.P.finite_quot_conjInter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:58.550569+00:00
-- url     : https://prove2.me/submissions/c3b371fb-5b3e-4fab-a6d2-eed66c155d1a

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset

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
theorem _root_.solution {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    Finite (K ⧸ conjInter K s) := by
  haveI : (conjInter K s).FiniteIndex := ⟨hK s⟩
  exact Subgroup.finite_quotient_of_finiteIndex
end Formalism.UG.P
