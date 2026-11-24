-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.pd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:21:23.615665+00:00
-- url     : https://prove2.me/submissions/404109ee-af66-4cf5-af8a-2c2b1aec42ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne

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
theorem _root_.solution {ι : Type} (i : ι) (x y : MvPowerSeries ι K) :
    pd i (x * y) = x * pd i y + y * pd i x := by
  simp only [Formalism.L2.Th1.B.pd, Derivation.leibniz, smul_eq_mul]
end Formalism.L2.Th1.B.Add1
