-- Prove2me | solution 1 for Formalism.L2.Th1.B.Split.cong_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:55:44.40667+00:00
-- url     : https://prove2.me/submissions/563d4675-2fea-49a6-b3d7-7f842f01654e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
import Theorems.Thm_Formalism_L2_Th1_C_lGBinom


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
theorem _root_.solution {σ : Type} {z : K} (hz : IsBinomScalar R z) {f g : MvPowerSeries σ K}
    (h : Cong R f g) : Cong R (z • f) (z • g) := by
  have := lGBinom K R σ z hz _ h
  unfold Cong
  rwa [← smul_sub]
end Formalism.L2.Th1.B.Split
