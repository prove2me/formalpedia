-- Prove2me | solution 1 for Formalism.Q3.hostFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:30.72484+00:00
-- url     : https://prove2.me/submissions/94620db3-e5d5-4067-bc52-0c29acf7c8cb

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
import Theorems.Thm_Formalism_Q3_mqFrob
import Theorems.Thm_Formalism_Q3_hostGalois
import Theorems.Thm_Formalism_Q3_hostFrob_of
import Theorems.Thm_Formalism_Q3_kroneckerMeaning


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
theorem _root_.solution : HostFrob := hostFrob_of mqFrob hostGalois kroneckerMeaning
end Formalism.Q3
