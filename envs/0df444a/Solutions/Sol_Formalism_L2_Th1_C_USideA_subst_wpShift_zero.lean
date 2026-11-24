-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.subst_wpShift_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:01.293899+00:00
-- url     : https://prove2.me/submissions/8efbc824-3d60-4270-9ffd-d5df973203a1

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
theorem _root_.solution {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (e : PowerSeries K) :
    PowerSeries.subst a (wpShift e 0) = 1 + a ^ 2 * PowerSeries.subst a e := by
  unfold wpShift
  rw [← PowerSeries.coe_substAlgHom ha]
  simp only [map_add, map_one, map_mul, map_pow, map_sub, map_zero, sub_zero,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
end Formalism.L2.Th1.C.USideA
