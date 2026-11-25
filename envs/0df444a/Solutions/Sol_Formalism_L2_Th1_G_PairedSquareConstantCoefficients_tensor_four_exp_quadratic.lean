-- Prove2me | solution 1 for Formalism.L2.Th1.G.PairedSquareConstantCoefficients.tensor_four_exp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:57:58.478547+00:00
-- url     : https://prove2.me/submissions/c2e17ddc-84de-4ab1-b44b-dc671a166029

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
import Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_constantCoeff_C_mul_sqSum
import Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_constantCoeff_inBlock
import Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_sum_inBlock_sqSum
import Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_inBlock_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_sum


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
variable [CharZero K]
namespace Formalism.L2.Th1.G.PairedSquareConstantCoefficients
theorem _root_.solution {ι : Type} [Fintype ι] (s : K) (c : ι → K) :
    tens4 (mvExp (MvPowerSeries.C s * sqSum c)) =
      mvExp (MvPowerSeries.C s * sqSum (fun a : Fin 4 × ι => c a.2)) := by
  unfold tens4
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.C s * sqSum c) = 0 :=
    constantCoeff_C_mul_sqSum s c
  rw [Finset.prod_congr rfl (fun k _ => inBlock_mvExp k h0),
    ← mvExp_sum Finset.univ (fun k : Fin 4 => inBlock k (MvPowerSeries.C s * sqSum c))
      (fun k _ => constantCoeff_inBlock k h0),
    sum_inBlock_sqSum]
end Formalism.L2.Th1.G.PairedSquareConstantCoefficients
