-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.cc_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:32.797789+00:00
-- url     : https://prove2.me/submissions/8995fa8c-bf16-4966-bb7d-6958fffd2a60

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
    PowerSeries.constantCoeff (mulBy l linv al) = 0 := by
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr h.2.2.1
  have ha : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  unfold mulBy
  rw [hq, ← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha, map_mul, map_mul, h.1, mul_zero, zero_mul]
end Formalism.L2.Th1.C.USideA
