-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:33.813111+00:00
-- url     : https://prove2.me/submissions/ec084d50-7ff4-45cd-bcdb-41f4d3e12ba9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn_subst_one
import Theorems.Thm_Formalism_L2_Th1_G_jetsIn1_exp
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
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {ι : Type}
namespace Formalism.L2.Th1.G
theorem _root_.solution {a : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff a = 0)
    (ha : JetsIn R a) : JetsIn R (Formalism.L2.Th1.C.mvExp a) := jetsIn_subst_one jetsIn1_exp h0 ha
end Formalism.L2.Th1.G
