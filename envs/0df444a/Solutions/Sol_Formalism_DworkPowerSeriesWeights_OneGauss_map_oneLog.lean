-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.map_oneLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:45.4718+00:00
-- url     : https://prove2.me/submissions/6df9c9a6-0514-4d54-8695-a9543e4f80ea

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution {F K : Type} [Field F] [Field K] (φ : F →+* K) {τ : Type} [DecidableEq τ]
    (l : ℕ) (x : τ) : MvPowerSeries.map φ (oneLog (K := F) l x) = oneLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (oneLog (K := F) l x n) = oneLog (K := K) l x n
  simp [oneLog, map_sum, apply_ite]
end Formalism.DworkPowerSeriesWeights.OneGauss
