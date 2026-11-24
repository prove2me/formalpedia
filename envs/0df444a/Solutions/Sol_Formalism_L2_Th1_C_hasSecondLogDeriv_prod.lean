-- Prove2me | solution 1 for Formalism.L2.Th1.C.hasSecondLogDeriv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:35:31.849059+00:00
-- url     : https://prove2.me/submissions/8233f264-535f-479c-983c-3532508ca1f0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
import Theorems.Thm_Formalism_L2_Th1_C_hasSecondLogDeriv_one
import Theorems.Thm_Formalism_L2_Th1_C_hasSecondLogDeriv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C
theorem _root_.solution {ι : Type} (s : Finset ι) (f g : ι → PowerSeries K)
    (h : ∀ i ∈ s, HasSecondLogDeriv (f i) (g i)) : HasSecondLogDeriv (∏ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    exact hasSecondLogDeriv_one
  · intro a s ha ih hh
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact hasSecondLogDeriv_mul (hh a (Finset.mem_insert_self a s))
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))
end Formalism.L2.Th1.C
