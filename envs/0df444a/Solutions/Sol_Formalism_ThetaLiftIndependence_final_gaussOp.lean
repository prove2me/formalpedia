-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.final_gaussOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:34:32.565138+00:00
-- url     : https://prove2.me/submissions/aa6a9f7a-3582-475b-a39f-dd7b0f99b8b4

import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_OrbitSum
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_EigenSwap
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_DetSwap
import Definitions.Def_Formalism_ThetaLiftIndependence_FinalThetaLiftAMFKIndep
import Theorems.Thm_Formalism_ThetaLiftIndependence_gaussOp_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
namespace Formalism.ThetaLiftIndependence
theorem _root_.solution : GaussOp := gaussOp_eq
end Formalism.ThetaLiftIndependence
