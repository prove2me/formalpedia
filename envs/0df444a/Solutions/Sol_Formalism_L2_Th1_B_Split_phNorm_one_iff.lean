-- Prove2me | solution 1 for Formalism.L2.Th1.B.Split.phNorm_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:51:31.260581+00:00
-- url     : https://prove2.me/submissions/487948b3-de10-4c08-805a-131d5a7bfa09

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_mulBy_eq_fmul


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Split
open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}
namespace Formalism.L2.Th1.B.Split
theorem _root_.solution (c : K) :
    PhNormAt R l linv ph c 1 ↔
      Cong R (PowerSeries.subst (fmul l linv c (PowerSeries.X : MvPowerSeries Unit K)) ph)
        (c • (ph : MvPowerSeries Unit K)) := by
  rw [PhNormAt, mulBy_eq_fmul, mul_one]
end Formalism.L2.Th1.B.Split
