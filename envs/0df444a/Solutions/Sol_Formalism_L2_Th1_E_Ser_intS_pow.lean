-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.intS_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:40.63319+00:00
-- url     : https://prove2.me/submissions/8f6849dc-fc13-484f-9c22-fe8e88a210d5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_one
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_mul

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
theorem _root_.solution {f : K⟦X⟧} (hf : IntS f) (n : ℕ) : IntS (f ^ n) := by
  induction n with
  | zero => simpa using intS_one (K := K)
  | succ n ih => rw [pow_succ]; exact intS_mul ih hf
end Formalism.L2.Th1.E.Ser
