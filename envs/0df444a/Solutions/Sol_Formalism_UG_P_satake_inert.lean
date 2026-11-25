-- Prove2me | solution 1 for Formalism.UG.P.satake_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:16.46015+00:00
-- url     : https://prove2.me/submissions/4ecc2e27-5066-49a9-a9dd-cb3bca8aa3bc

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Fcompose
import Theorems.Thm_Formalism_UG_P_exists_spherical_function_unitary
import Theorems.Thm_Formalism_UG_P_satake_transform_inert_prime


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
theorem _root_.solution : Formalism.UG.SatakeInert := satake_transform_inert_prime exists_spherical_function_unitary
end Formalism.UG.P
