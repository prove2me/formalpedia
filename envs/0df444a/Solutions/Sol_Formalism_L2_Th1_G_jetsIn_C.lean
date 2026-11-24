-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:02.24129+00:00
-- url     : https://prove2.me/submissions/382a6db6-513b-4353-9e2e-07947b5867cc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_mfact_zero
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
theorem _root_.solution {c : K} (hc : c ∈ R) : JetsIn R (MvPowerSeries.C c : MvPowerSeries ι K) := by
  intro κ
  classical
  by_cases h : κ = 0
  · subst h
    simpa [mfact_zero] using hc
  · simp [MvPowerSeries.coeff_C, h]
end Formalism.L2.Th1.G
