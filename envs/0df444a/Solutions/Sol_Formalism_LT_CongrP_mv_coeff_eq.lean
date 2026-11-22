-- Prove2me | solution 1 for Formalism.LT.CongrP.mv_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:54.707166+00:00
-- url     : https://prove2.me/submissions/1617abbb-2592-4515-ac12-6a6beac61b69

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.CongrP
theorem _root_.solution (φ : PowerSeries K) (d : Unit →₀ ℕ) :
    MvPowerSeries.coeff d φ = coeff (d ()) φ := by
  conv_lhs => rw [Finsupp.unique_single d]
  rfl
end Formalism.LT.CongrP
