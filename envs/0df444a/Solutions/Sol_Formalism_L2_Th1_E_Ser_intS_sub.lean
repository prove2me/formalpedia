-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.intS_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:44.917057+00:00
-- url     : https://prove2.me/submissions/d4ae67c1-6268-49d1-a826-8efa58397753

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_add
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_neg

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
theorem _root_.solution {f g : K⟦X⟧} (hf : IntS f) (hg : IntS g) : IntS (f - g) := by
  rw [sub_eq_add_neg]
  exact intS_add hf (intS_neg hg)
end Formalism.L2.Th1.E.Ser
