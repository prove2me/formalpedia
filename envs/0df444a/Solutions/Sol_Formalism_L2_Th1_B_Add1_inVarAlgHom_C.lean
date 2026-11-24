-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.inVarAlgHom_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:20.219813+00:00
-- url     : https://prove2.me/submissions/f4ca0ec9-9d33-481b-8f26-5bba6e42cc12

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
import Theorems.Thm_Formalism_L2_Th1_B_Add1_triple_lintegral_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add1
theorem _root_.solution {ι : Type} (x : ι) (c : K) :
    at1H x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  rw [← triple_lintegral_eq]
  exact PowerSeries.subst_C c
end Formalism.L2.Th1.B.Add1
