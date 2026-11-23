-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rowDeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:02.501529+00:00
-- url     : https://prove2.me/submissions/fc9cbd0a-2223-438c-9d30-3a038d15a1a8

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
theorem _root_.solution {d N0 N1 : ℕ} (s : ZMod d) (k : Fin N0) (a b : ZV d N0 N1 →₀ ℕ) :
    rowDeg s k (a + b) = rowDeg s k a + rowDeg s k b := by
  simp [rowDeg, Finset.sum_add_distrib]
end Formalism.DworkPowerSeriesWeights
