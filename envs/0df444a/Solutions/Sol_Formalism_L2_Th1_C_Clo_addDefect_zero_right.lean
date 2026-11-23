-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.addDefect_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:29.742209+00:00
-- url     : https://prove2.me/submissions/5ef21c5b-15a6-44a2-a1a2-3b3c04b1ab01

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_zero


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}
variable [CharZero K] {ph : PowerSeries K} {σ : Type}
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution (h : Frame R l linv ph) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : be0 l linv ph x 0 = 0 := by
  rw [be0, Pts.fadd_zero h.1 hx, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2, sub_self,
    sub_zero]
end Formalism.L2.Th1.C.Clo
