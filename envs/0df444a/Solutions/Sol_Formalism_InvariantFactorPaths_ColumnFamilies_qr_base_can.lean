-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_base_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.019898+00:00
-- url     : https://prove2.me/submissions/5c24d42f-a521-4c16-967d-92d73915e04e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral

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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (c : ℤ) : qr_base (canT nu) c = qr_can nu c := by
  unfold qr_base
  split_ifs <;> rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
