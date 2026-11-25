-- Prove2me | solution 1 for Formalism.L2.Th1.B.KSum.coeff_two_pSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:36.442528+00:00
-- url     : https://prove2.me/submissions/d4a32b72-4f30-4f6a-acf2-93ec7f1425aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_GoodModelLattice
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_CoeffTwoPSeries
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_F_pSeriesCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KSum
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
namespace Formalism.L2.Th1.B.KSum
theorem _root_.solution (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by
  rw [Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]
  first
    | (simp only [PeriodPair.g₂]; push_cast; ring)
    | (unfold PeriodPair.g₂; push_cast; ring)
    | (norm_num [PeriodPair.g₂]; ring)
end Formalism.L2.Th1.B.KSum
