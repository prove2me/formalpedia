-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:26.505724+00:00
-- url     : https://prove2.me/submissions/47a85962-e9d5-435d-91ff-514813ec5d42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_one
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
variable {K : Type} [Field K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K)
    (hf : ∀ a ∈ s, JetsIn R (f a)) : JetsIn R (∏ a ∈ s, f a) := by
  exact Finset.prod_induction f (JetsIn R) (fun a b ha hb => jetsIn_mul ha hb)
    jetsIn_one hf
end Formalism.L2.Th1.G
