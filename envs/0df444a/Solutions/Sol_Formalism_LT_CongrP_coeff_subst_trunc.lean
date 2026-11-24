-- Prove2me | solution 1 for Formalism.LT.CongrP.coeff_subst_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:45.21879+00:00
-- url     : https://prove2.me/submissions/5d8d190d-fdcc-4a9b-986c-a4270bae4ee6

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_coeff_subst_range
import Theorems.Thm_Formalism_LT_CongrP_constantCoeff_trunc_succ

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
variable {R : Type*} [CommRing R]
namespace Formalism.LT.CongrP
theorem _root_.solution (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst (trunc (N + 1) a : PowerSeries R)) = coeff N (f.subst a) := by
  rw [coeff_subst_range f _ (constantCoeff_trunc_succ a ha N), coeff_subst_range f a ha]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self N) (f := (trunc (N + 1) a : PowerSeries R) ^ n),
    trunc_trunc_pow, coeff_coe_trunc_of_lt (Nat.lt_succ_self N)]
end Formalism.LT.CongrP
