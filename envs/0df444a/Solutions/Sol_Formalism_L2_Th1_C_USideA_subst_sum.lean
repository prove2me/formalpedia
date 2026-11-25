-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.subst_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:31.677385+00:00
-- url     : https://prove2.me/submissions/ed558c1e-fe92-49f3-b9e3-38942b345b95

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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideA
theorem _root_.solution {ι : Type} {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (s : Finset ι)
    (F : ι → PowerSeries K) :
    PowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, PowerSeries.subst a (F i) := by
  rw [← PowerSeries.coe_substAlgHom ha, map_sum]
end Formalism.L2.Th1.C.USideA
