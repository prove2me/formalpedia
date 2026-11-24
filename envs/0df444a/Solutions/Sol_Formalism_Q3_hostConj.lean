-- Prove2me | solution 1 for Formalism.Q3.hostConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:29.882349+00:00
-- url     : https://prove2.me/submissions/eea3c62f-6984-4c4d-a3e1-e0935d732dae

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
import Theorems.Thm_Formalism_Q3_mqKummer
import Theorems.Thm_Formalism_Q3_hostGalois
import Theorems.Thm_Formalism_Q3_hostConj_of


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
theorem _root_.solution : HostConj := hostConj_of hostGalois mqKummer
end Formalism.Q3
