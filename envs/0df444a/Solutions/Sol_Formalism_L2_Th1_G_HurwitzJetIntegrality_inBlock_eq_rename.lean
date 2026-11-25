-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.inBlock_eq_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:19.743806+00:00
-- url     : https://prove2.me/submissions/e38f35e2-f8c8-46ad-b606-e2d825123f71

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB

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
open Formalism.L2.Th1.G.HurwitzJetIntegrality
namespace Formalism.L2.Th1.G.HurwitzJetIntegrality
theorem _root_.solution {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K) :
    inBlock k f = MvPowerSeries.rename (blockEmb B ι k) f := by
  unfold inBlock
  first
    | exact (MvPowerSeries.rename_eq_subst (blockEmb B ι k) f).symm
    | exact (MvPowerSeries.rename_eq_subst f (blockEmb B ι k)).symm
    | (rw [MvPowerSeries.rename_eq_subst]; rfl)
    | rfl
end Formalism.L2.Th1.G.HurwitzJetIntegrality
