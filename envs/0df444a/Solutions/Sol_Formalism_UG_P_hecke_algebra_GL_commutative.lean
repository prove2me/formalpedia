-- Prove2me | solution 1 for Formalism.UG.P.hecke_algebra_GL_commutative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:54:03.601853+00:00
-- url     : https://prove2.me/submissions/80020c24-04df-4ff8-af81-6bcb872c67c7

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ecompose
import Theorems.Thm_Formalism_UG_P_cartan_decomposition_holds
import Theorems.Thm_Formalism_UG_P_hecke_algebra_GL_comm_of_cartan


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HeckeCommGL := hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds
end Formalism.UG.P
