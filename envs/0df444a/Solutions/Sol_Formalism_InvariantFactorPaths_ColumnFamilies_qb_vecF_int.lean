-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_vecF_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:11.531828+00:00
-- url     : https://prove2.me/submissions/b4f42147-b7fb-432c-afe4-b0223ad26c17

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) : qb_vecF CF ℤ = fun x => CF.vec x.1 x.2.1 := by
  funext x i
  simp [qb_vecF]
end Formalism.InvariantFactorPaths.ColumnFamilies
