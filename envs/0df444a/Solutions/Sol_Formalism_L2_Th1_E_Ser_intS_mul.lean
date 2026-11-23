-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.intS_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:25.718402+00:00
-- url     : https://prove2.me/submissions/c3be524b-6ac5-4fcf-9c06-77e232abffd8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_norm_sum_le_one
import Theorems.Thm_Formalism_L2_Th1_E_Ser_norm_mul_le_one

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
theorem _root_.solution {f g : K⟦X⟧} (hf : IntS f) (hg : IntS g) : IntS (f * g) := by
  intro n
  rw [coeff_mul]
  exact norm_sum_le_one _ _ (fun p _ => norm_mul_le_one (hf _) (hg _))
end Formalism.L2.Th1.E.Ser
