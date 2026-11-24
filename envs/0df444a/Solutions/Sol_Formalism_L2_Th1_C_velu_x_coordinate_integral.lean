-- Prove2me | solution 1 for Formalism.L2.Th1.C.velu_x_coordinate_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:51:13.019432+00:00
-- url     : https://prove2.me/submissions/55f0f695-bcfe-4177-b966-e61307bcd6e9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_int_of_eq
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_isOneUnit_veluXs

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
open CompactOperatorsAlt
namespace Formalism.L2.Th1.C
theorem _root_.solution : VeluIntegralX := by
  intro K _ _ R A g ι _ xs xP al r hA hxs hxP hr hal hal0 h2 hg0 hEq
  refine int_of_eq h2 two_ne_zero hA.2 (isOneUnit_veluXs hA hxs hxP hr) hal hg0 ?_
  have hC : (C (al ^ 2) : PowerSeries K) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [constantCoeff_C, map_zero] at this
    exact pow_ne_zero 2 hal0 this
  have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h0 : C (al ^ 2) * X ^ 2 *
      (A.subst (C al * X * g) - g * g * veluXs A xs xP r) = 0 := by
    have : C (al ^ 2) * X ^ 2 * (A.subst (C al * X * g) - g * g * veluXs A xs xP r) =
        C (al ^ 2) * A.subst (C al * X * g) * X ^ 2 -
          (C al * X * g) ^ 2 * veluXs A xs xP r := by
      rw [map_pow]; ring
    rw [this, hEq, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero hC hX))
end Formalism.L2.Th1.C
