-- Prove2me | solution 1 for Formalism.L2.Th1.G.jets_ring_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:27.067111+00:00
-- url     : https://prove2.me/submissions/e748f44b-01e1-4165-ad83-ceccdaa56fc2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_C
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_X
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_add
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_neg
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single


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
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
namespace Formalism.L2.Th1.G
theorem _root_.solution : JetsRing := by
  intro K _ R ι
  exact ⟨fun c hc => jetsIn_C hc, jetsIn_X, fun f g => jetsIn_add, fun f => jetsIn_neg,
    fun f g => jetsIn_mul⟩
end Formalism.L2.Th1.G
