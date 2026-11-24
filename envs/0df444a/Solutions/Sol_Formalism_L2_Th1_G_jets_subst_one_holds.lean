-- Prove2me | solution 1 for Formalism.L2.Th1.G.jets_subst_one_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:42.795026+00:00
-- url     : https://prove2.me/submissions/a9b33738-f51c-4db1-8f83-d231887dc9ca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_subst_one
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
theorem _root_.solution : JetsSubstOne := by
  intro K _ _ R ι f a hf h0 ha
  exact jetsIn_subst_one hf h0 ha
end Formalism.L2.Th1.G
