-- Prove2me | solution 1 for Formalism.UG.P.satake_transform_hecke_operator_Tj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:04.789502+00:00
-- url     : https://prove2.me/submissions/17799811-64cc-4790-bf32-5cd280d2f5f4

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ecompose
import Theorems.Thm_Formalism_UG_P_Tj_double_coset_decomposition
import Theorems.Thm_Formalism_UG_P_exists_spherical_function
import Theorems.Thm_Formalism_UG_P_satake_Tj_of_spherical_cosets


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
theorem _root_.solution : Formalism.UG.SatakeTj := satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition
end Formalism.UG.P
