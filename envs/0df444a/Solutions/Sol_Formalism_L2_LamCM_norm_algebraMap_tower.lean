-- Prove2me | solution 1 for Formalism.L2.LamCM.norm_algebraMap_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:17.09846+00:00
-- url     : https://prove2.me/submissions/9d4c41c7-b63a-4eef-b3ad-f9ed52380e7e

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution (x : K) :
    Algebra.norm ℚ (algebraMap K K1 x) = (Algebra.norm ℚ x) ^ Module.finrank K K1 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := K) (a := algebraMap K K1 x), Algebra.norm_algebraMap, map_pow]
end Formalism.L2.LamCM
