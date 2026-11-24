-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.intPS_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:10.367947+00:00
-- url     : https://prove2.me/submissions/8972f448-f76e-4df1-a585-1281b9b1acb2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_X_pow

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
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.USideA
theorem _root_.solution : IntPS R (PowerSeries.X : PowerSeries K) := by
  simpa using (intPS_X_pow 1 : IntPS R (PowerSeries.X ^ 1 : PowerSeries K))
end Formalism.L2.Th1.C.USideA
