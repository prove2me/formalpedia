-- Prove2me | solution 1 for Formalism.LT.LTL.coeff_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:14.989908+00:00
-- url     : https://prove2.me/submissions/74ba0911-5648-46bd-a6a6-9f736ff29222

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

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
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
namespace Formalism.LT.LTL
theorem _root_.solution (a : ι → K) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (lin a) = ∑ i, a i * (if d = Finsupp.single i 1 then 1 else 0) := by
  simp only [lin, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X]
end Formalism.LT.LTL
