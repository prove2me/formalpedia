-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.kapC_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:41.413009+00:00
-- url     : https://prove2.me/submissions/1cff8060-a33a-4d9e-a9c3-9493fbfe7d56

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {p n n' d d' : ℕ} (hn : n ≤ n') (hd : d ≤ d') : kapC p n d ≤ kapC p n' d' := by
  unfold kapC
  exact Nat.mul_le_mul (Nat.choose_le_choose 2 hn) (Nat.log_mono_right (by omega))
end Formalism.InvariantFactorPaths.PW
