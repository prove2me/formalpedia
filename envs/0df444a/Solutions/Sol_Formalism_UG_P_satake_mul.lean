-- Prove2me | solution 1 for Formalism.UG.P.satake_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:50.60258+00:00
-- url     : https://prove2.me/submissions/ab2e2203-066e-4c0c-9dcb-9abc7aeb71b9

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Fcompose
import Theorems.Thm_Formalism_UG_P_exists_spherical_function_unitary
import Theorems.Thm_Formalism_UG_P_satake_transform_multiplicative


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
theorem _root_.solution : Formalism.UG.SatMul := satake_transform_multiplicative exists_spherical_function_unitary
end Formalism.UG.P
