-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:44.014798+00:00
-- url     : https://prove2.me/submissions/c0ad4163-a4df-40a8-a124-ac8fcb781d12

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
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    vla la I ≠ 0 ↔ la.asIdeal ∣ I := by
    unfold vla
    exact Associates.count_ne_zero_iff_dvd hI la.irreducible
end Formalism.L2.Pj.QAt.BeSumPf
