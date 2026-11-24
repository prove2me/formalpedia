-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.psubst_fLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:21.862659+00:00
-- url     : https://prove2.me/submissions/7634ffde-3ce1-43f3-917a-451d4f76696f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_psubst_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution {l g : PowerSeries K} (hl : constantCoeff l = 0) (hg : constantCoeff g = 1) :
    subst l (fLog g) = fLog (subst l g) := by
  have h1 : constantCoeff (g - 1) = 0 := by rw [map_sub, hg, map_one, sub_self]
  unfold fLog
  rw [subst_comp_subst_apply (hs h1) (hs hl), subst_sub (hs hl), psubst_one (hs hl)]
end Formalism.L2.Th1.B.Ph
