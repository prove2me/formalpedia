-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.intS_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:57.337842+00:00
-- url     : https://prove2.me/submissions/450db4ea-8913-4f37-82b8-ccfd95ed7a10

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution : IntS (1 : K⟦X⟧) := by
  have := intS_C (K := K) (a := 1) (by simp)
  simpa using this
end Formalism.L2.Th1.E.Ser
