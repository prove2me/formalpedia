-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.opA_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.973873+00:00
-- url     : https://prove2.me/submissions/845189a8-7cf7-481b-9792-0ad3500f7060

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
theorem _root_.solution {K : Type u} [NormedField K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (hT : ∀ s i k, ‖T s i k‖ ≤ 1) (s : ZMod d) (i k : Fin N0) :
    ‖opA TT T s i k‖ ≤ 1 := by
  unfold opA
  split_ifs <;> simp [hT]
end Formalism.DworkPowerSeriesWeights
