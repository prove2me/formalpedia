-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.BeSumPf.maxPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:46.385946+00:00
-- url     : https://prove2.me/submissions/82abb7b1-4e0d-4eef-9695-8ede0aeaaf21

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
open Formalism.L2.Pj.QAt.BeSumPf
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.Pj.QAt.BeSumPf
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) :
    v.maxPowDividing I = v.asIdeal ^ vla v I := rfl
end Formalism.L2.Pj.QAt.BeSumPf
