-- Prove2me | solution 1 for Formalism.L2.Th1.B.Split.lg_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:27.133302+00:00
-- url     : https://prove2.me/submissions/d883dcf4-0b39-4fbb-a912-1e65b562f09d

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
theorem _root_.solution {σ : Type} {c : K} (hc : c ≠ 0) (hz : IsBinomScalar R c⁻¹)
    {f : MvPowerSeries σ K} (h : LG R (c • f)) : LG R f := by
  have := lGBinom K R σ _ hz _ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
end Formalism.L2.Th1.B.Split
