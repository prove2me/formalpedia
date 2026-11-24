-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:07.517024+00:00
-- url     : https://prove2.me/submissions/12df0883-e3dc-447d-8869-c33f4457318c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_L2_Th1_G_mfact_single_one
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
theorem _root_.solution (i : ι) : JetsIn R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  intro κ
  classical
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h
    simp [mfact_single_one]
  · simp
end Formalism.L2.Th1.G
