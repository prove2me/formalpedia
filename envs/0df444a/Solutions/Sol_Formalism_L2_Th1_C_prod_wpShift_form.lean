-- Prove2me | solution 1 for Formalism.L2.Th1.C.prod_wpShift_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:10.694214+00:00
-- url     : https://prove2.me/submissions/13afb28c-34ed-47ae-8680-d4d53ce1bae8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp

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
theorem _root_.solution {ι : Type} (s : Finset ι) (e : PowerSeries K) (c : ι → K) :
    ∃ r : PowerSeries K, ∏ P ∈ s, wpShift e (c P) = 1 + X ^ 2 * r := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s ha ⟨r, hr⟩
  refine ⟨(e - C (c a)) + r + X ^ 2 * (e - C (c a)) * r, ?_⟩
  rw [Finset.prod_insert ha, hr, wpShift]
  ring
end Formalism.L2.Th1.C
