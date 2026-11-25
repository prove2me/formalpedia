-- Prove2me | solution 1 for Formalism.L2.Th1.G.PairedSquareConstantCoefficients.constantCoeff_inBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:43.063298+00:00
-- url     : https://prove2.me/submissions/34b15a17-e3aa-4843-8ba8-820412480875

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_coeff_inBlock_embDomain


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
theorem _root_.solution {ι B : Type} (k : B) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (inBlock k f) = 0 := by
  have h := HurwitzJetIntegrality.coeff_inBlock_embDomain k f 0
  rw [Finsupp.embDomain_zero] at h
  simpa [hf] using h
end Formalism.L2.Th1.G.PairedSquareConstantCoefficients
