-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_le_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:24.853533+00:00
-- url     : https://prove2.me/submissions/c616964a-02c9-46eb-a443-022ef42261d6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  rw [Fin.le_iff_val_le_val]
  show a.val ≤ n - 1
  have := a.isLt
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
