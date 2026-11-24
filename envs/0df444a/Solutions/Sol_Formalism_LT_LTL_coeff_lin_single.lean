-- Prove2me | solution 1 for Formalism.LT.LTL.coeff_lin_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:27.335564+00:00
-- url     : https://prove2.me/submissions/ffc38e13-adc4-43ea-935e-18785924eaaf

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_coeff_lin

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
theorem _root_.solution (a : ι → K) (i : ι) :
    MvPowerSeries.coeff (Finsupp.single i 1) (lin a) = a i := by
  rw [coeff_lin]
  simp [Finsupp.single_left_inj one_ne_zero]
end Formalism.LT.LTL
