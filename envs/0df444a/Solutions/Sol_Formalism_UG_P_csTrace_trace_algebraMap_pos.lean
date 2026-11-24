-- Prove2me | solution 1 for Formalism.UG.P.csTrace_trace_algebraMap_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:06.801266+00:00
-- url     : https://prove2.me/submissions/035eb6ab-d114-4e87-b6a6-337e956ab230

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsTrace
import Theorems.Thm_Formalism_UG_P_csTrace_trace_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] (b : F) (hb : ∀ ι : F →+* ℝ, 0 < ι b) :
    0 < Algebra.trace ℚ E (algebraMap F E b) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]
  exact nsmul_pos (csTrace_trace_pos b hb) Module.finrank_pos.ne'
end Formalism.UG.P
