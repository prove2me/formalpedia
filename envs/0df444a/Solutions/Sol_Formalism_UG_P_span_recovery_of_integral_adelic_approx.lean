-- Prove2me | solution 1 for Formalism.UG.P.span_recovery_of_integral_adelic_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:08.602387+00:00
-- url     : https://prove2.me/submissions/ba71f9c8-17a7-4b2a-9fc4-fa2762f78c2d

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Theorems.Thm_Formalism_UG_P_csSpan_fwd
import Theorems.Thm_Formalism_UG_P_csSpan_back

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (hIntAdApprox : Formalism.UG.CS.IntAdApprox) : Formalism.UG.CS.SpanRecover := by
  intro F E _ _ _ _ _ n _ _ Λ hfin hspan g u
  exact ⟨csSpan_fwd Λ g u, csSpan_back hIntAdApprox Λ hfin hspan g u⟩
end Formalism.UG.P
