-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.intPS_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:14.129985+00:00
-- url     : https://prove2.me/submissions/572bccb9-2897-435c-8d5e-05527adb9f15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA

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
theorem _root_.solution {ι : Type} (s : Finset ι) {F : ι → PowerSeries K} (hF : ∀ i ∈ s, IntPS R (F i)) :
    IntPS R (∑ i ∈ s, F i) := fun n => by
  rw [map_sum]
  exact R.sum_mem (fun i hi => hF i hi n)
end Formalism.L2.Th1.C.USideA
