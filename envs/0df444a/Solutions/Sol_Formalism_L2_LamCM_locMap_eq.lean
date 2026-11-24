-- Prove2me | solution 1 for Formalism.L2.LamCM.locMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:58.154939+00:00
-- url     : https://prove2.me/submissions/3fad6d4c-7962-4ddd-b9ec-1f1c9a162075

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
theorem _root_.solution :
    IsLocalization.map K1 (algebraMap (𝓞 K) (𝓞 K1)) (nzd_le (K := K) (K1 := K1)) = algebraMap K K1 := by
  apply IsLocalization.ringHom_ext (𝓞 K)⁰
  rw [IsLocalization.map_comp]
  ext a
  exact algebraMap_int_tower a
end Formalism.L2.LamCM
