-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:45.495316+00:00
-- url     : https://prove2.me/submissions/705d5957-9e5a-4b71-9054-483494a5c954

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul

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
open Formalism.DworkPowerSeriesWeights.OrbMul
namespace Formalism.DworkPowerSeriesWeights.OrbMul
theorem _root_.solution {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (x : ZV d N0 N1) :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) x = MvPowerSeries.X x := by
  classical
  unfold linSub idM
  simp
end Formalism.DworkPowerSeriesWeights.OrbMul
