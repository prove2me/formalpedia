-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.subst_mulBy_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:08.146042+00:00
-- url     : https://prove2.me/submissions/2c11809c-5967-4c91-b0b2-359f97df1455

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
import Theorems.Thm_Formalism_L2_Th1_C_USideB_hs_of

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
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideB
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have hb : PowerSeries.constantCoeff (PowerSeries.C al * l) = 0 := by simp [h.1]
  rw [mulBy, ← PowerSeries.subst_comp_subst_apply (hs_of h.2.2.1) (hs_of hb), h.2.2.2.2,
    PowerSeries.subst_X (hs_of hb)]
end Formalism.L2.Th1.C.USideB
