-- Prove2me | solution 1 for Formalism.L2.Th1.G.PairedSquareConstantCoefficients.biadd_formal_mul_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:57.929778+00:00
-- url     : https://prove2.me/submissions/62bbde13-8598-4c85-9f5c-bd7df1fc44d0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_zero_left
import Theorems.Thm_Formalism_L2_Th1_C_Pts_zero_fadd


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.L2.Th1.G.PairedSquareConstantCoefficients
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G.PairedSquareConstantCoefficients
theorem _root_.solution {l linv ph : PowerSeries K} (h : IsLogPair l linv)
    (hph : PowerSeries.constantCoeff ph = 0) {σ : Type} (x : MvPowerSeries σ K) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : be0 l linv ph (fmul l linv 0 x) y = 0 := by
  rw [Pts.fmul_zero_left h, be0, Pts.zero_fadd h hy, PowerSeries.subst_zero_of_constantCoeff_zero hph,
    sub_zero, sub_self]
end Formalism.L2.Th1.G.PairedSquareConstantCoefficients
