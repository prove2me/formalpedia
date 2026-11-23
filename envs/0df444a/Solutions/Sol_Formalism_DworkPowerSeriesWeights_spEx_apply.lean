-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spEx_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:46.650595+00:00
-- url     : https://prove2.me/submissions/503123fc-8104-47ac-8456-5f8b7fa0e8e8

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {m p : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (o : Option (Fin m)) (c c' : Fin (p + 1)) (k : Fin m) :
    spEx o c (k, c') = if o = some k ∧ c = c' then 1 else 0 := by
  cases o
  · simp [spEx]
  · simp [spEx, Finsupp.single_apply]
end Formalism.DworkPowerSeriesWeights
