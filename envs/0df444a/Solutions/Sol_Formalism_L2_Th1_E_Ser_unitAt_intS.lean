-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.unitAt_intS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:54.689354+00:00
-- url     : https://prove2.me/submissions/58d85046-1c20-4fdb-a2d0-9c43c31ac243

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_C
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_X
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_mul
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
theorem _root_.solution {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) : IntS f := by
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  exact intS_mul (intS_mul (intS_C ha.le) (intS_pow intS_X k)) hV.2
end Formalism.L2.Th1.E.Ser
