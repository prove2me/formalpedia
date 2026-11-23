-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frameM_idM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:02.397805+00:00
-- url     : https://prove2.me/submissions/d9a38ec8-e65a-4e30-b662-baac141557de

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval

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
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (x : ZMod d × Fin N0 × Fin N0 → K) (z i : ZV d N0 N1) :
    frameM (N1 := N1) x z i =
      ∑ y, (idM : ZV d N0 N1 → ZV d N0 N1 → K) z y * frameM (N1 := N1) x y i := by
  simp [idM]
end Formalism.DworkPowerSeriesWeights
