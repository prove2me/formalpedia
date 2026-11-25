-- Prove2me | solution 1 for Formalism.L2.Th1.G.jets_of_dist_jets_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:06:53.249803+00:00
-- url     : https://prove2.me/submissions/25a6124c-56ad-4f92-9123-5e7edbfa43ce

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_C_jetAdditive


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
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
namespace Formalism.L2.Th1.G
theorem _root_.solution : JetsOfDJets := by
  intro K _ _ R l linv f h
  unfold JetsIn1
  simp only [Formalism.L2.Th1.C.jetAdditive K l linv f h]
end Formalism.L2.Th1.G
