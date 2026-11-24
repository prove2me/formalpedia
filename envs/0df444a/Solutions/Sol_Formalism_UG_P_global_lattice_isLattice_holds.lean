-- Prove2me | solution 1 for Formalism.UG.P.global_lattice_isLattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:19.653158+00:00
-- url     : https://prove2.me/submissions/d67a2d2a-0252-4fc1-8e2d-0eac1d5af44b

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_csGlob_lattice

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
theorem _root_.solution : Formalism.UG.CS.GlobLatLattice := by
  intro F E _ _ _ _ _ n _ _ Λ hfin hspan g
  exact csGlob_lattice Λ hfin hspan g
end Formalism.UG.P
