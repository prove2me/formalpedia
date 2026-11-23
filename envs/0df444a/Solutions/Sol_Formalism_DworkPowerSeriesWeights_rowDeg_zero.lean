-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rowDeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:45.693219+00:00
-- url     : https://prove2.me/submissions/e7abc95c-0e58-4657-8ba4-703a6a036b3c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d N0 N1 : ℕ} (s : ZMod d) (k : Fin N0) :
    rowDeg (N1 := N1) s k 0 = 0 := by
  simp [rowDeg]
end Formalism.DworkPowerSeriesWeights
