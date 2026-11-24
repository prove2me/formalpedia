-- Prove2me | solution 1 for Formalism.UG.polyRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:36:16.912656+00:00
-- url     : https://prove2.me/submissions/d691bcf0-76ba-454b-8e79-a9cf432c7547

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_SatakeDualWeyl_NablaRepApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG
namespace Formalism.UG
theorem _root_.solution (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (g : GL n O) : polyRep O n g = (polyAct O n g).toLinearMap := rfl
end Formalism.UG
