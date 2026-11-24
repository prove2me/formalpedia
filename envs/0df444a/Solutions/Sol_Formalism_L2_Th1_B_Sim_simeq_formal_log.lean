-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sim.simeq_formal_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:21.935469+00:00
-- url     : https://prove2.me/submissions/485c1f70-e69d-4893-ae0a-cbb5b0577e02

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SimeqPadicIntegers
import Theorems.Thm_Formalism_L2_Th1_B_Sim_simeq_iff
import Theorems.Thm_Formalism_L2_Th1_B_Sim_inLam_fLog
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_add
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_inLam_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sim
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)
namespace Formalism.L2.Th1.B.Sim
theorem _root_.solution : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h
end Formalism.L2.Th1.B.Sim
