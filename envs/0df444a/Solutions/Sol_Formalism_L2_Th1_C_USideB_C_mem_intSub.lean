-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.C_mem_intSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:02.123522+00:00
-- url     : https://prove2.me/submissions/a9495d68-4a3a-48ba-bd6b-2d9dbdff3616

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
import Theorems.Thm_Formalism_L2_Th1_C_USideB_mem_intSub

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
open USideB
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideB
theorem _root_.solution {R : Subring K} {a : K} (ha : a ∈ R) : PowerSeries.C a ∈ intSub R := by
  refine mem_intSub.2 fun n => ?_
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem
end Formalism.L2.Th1.C.USideB
