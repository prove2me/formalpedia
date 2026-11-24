-- Prove2me | solution 1 for Formalism.Q3.mqKummer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:24.666804+00:00
-- url     : https://prove2.me/submissions/1c194e53-074f-404d-bab2-aafd60da959f

import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostFrob
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostEmb
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Theorems.Thm_Formalism_Q3_mqGalois
import Theorems.Thm_Formalism_Q3_mqKummer_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution : MQKummer := mqKummer_of mqGalois
end Formalism.Q3
