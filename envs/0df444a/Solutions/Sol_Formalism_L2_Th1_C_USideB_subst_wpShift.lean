-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.subst_wpShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:09.098616+00:00
-- url     : https://prove2.me/submissions/448a993a-8ee7-4ed6-823d-0eecd7c78d22

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
theorem _root_.solution {e l A : PowerSeries K} {c0 : K} (hl : PowerSeries.constantCoeff l = 0)
    (hX : XIsWp e l A c0) (x : K) :
    PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e (x + c0)) =
      (A - PowerSeries.C x * PowerSeries.X ^ 2) * l ^ 2 := by
  have hs := hs_of hl
  have e1 : wpShift e (x + c0) = wpShift e 0 - PowerSeries.C (x + c0) * PowerSeries.X ^ 2 := by
    simp only [wpShift, map_zero, sub_zero]
    ring
  have e2 : PowerSeries.subst l (wpShift e (x + c0)) =
      PowerSeries.subst l (wpShift e 0) - PowerSeries.C (x + c0) * l ^ 2 := by
    rw [e1, PowerSeries.subst_sub hs, PowerSeries.subst_mul hs, PowerSeries.subst_C,
      PowerSeries.subst_pow hs, PowerSeries.subst_X hs]
    rfl
  rw [e2, mul_sub, ← hX, map_add]
  ring
end Formalism.L2.Th1.C.USideB
