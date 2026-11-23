-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.subst_mulBy_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:33.547437+00:00
-- url     : https://prove2.me/submissions/98fedbf5-e449-4b29-a0f6-b043cbe3483d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
import Theorems.Thm_Formalism_L2_Th1_C_USideA_hs_of

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
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have ha : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  have hlinv : PowerSeries.HasSubst linv := hs_of h.2.2.1
  unfold mulBy
  rw [← PowerSeries.subst_comp_subst_apply hlinv ha, h.2.2.2.2, PowerSeries.subst_X ha]
end Formalism.L2.Th1.C.USideA
