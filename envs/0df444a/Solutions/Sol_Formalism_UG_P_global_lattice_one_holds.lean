-- Prove2me | solution 1 for Formalism.UG.P.global_lattice_one_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:54:20.675661+00:00
-- url     : https://prove2.me/submissions/28865895-5d24-4a1e-a8fd-59440eee823a

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_csGlob_one
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox


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
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.GlobLatOne := by
  intro F E _ _ _ _ _ n _ _ Λ hfin hspan
  exact csGlob_one csGlob_intAdApprox Λ hfin hspan
end Formalism.UG.P
