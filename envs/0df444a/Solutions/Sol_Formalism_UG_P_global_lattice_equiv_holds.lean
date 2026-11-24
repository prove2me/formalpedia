-- Prove2me | solution 1 for Formalism.UG.P.global_lattice_equiv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:10.109858+00:00
-- url     : https://prove2.me/submissions/f0acbf5d-1833-476f-9e5b-518deff2f7de

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEquiv
import Theorems.Thm_Formalism_UG_P_csEquiv_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG Formalism.UG.CS
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.GlobLatEquiv := by
  intro F E _ _ _ _ _ n _ _ Λ γ g k hk
  exact csEquiv_main Λ γ g k hk
end Formalism.UG.P
