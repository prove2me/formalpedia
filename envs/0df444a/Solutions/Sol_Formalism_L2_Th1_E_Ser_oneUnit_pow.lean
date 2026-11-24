-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.oneUnit_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:57.954724+00:00
-- url     : https://prove2.me/submissions/3a86c359-e2fe-4a47-a661-52827db1a4d6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_pow

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
theorem _root_.solution {f : K⟦X⟧} (hf : OneUnit f) (n : ℕ) : OneUnit (f ^ n) :=
  ⟨by rw [map_pow, hf.1, one_pow], intS_pow hf.2 n⟩
end Formalism.L2.Th1.E.Ser
