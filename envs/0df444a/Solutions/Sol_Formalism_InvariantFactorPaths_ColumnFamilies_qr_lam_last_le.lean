-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_lam_last_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:11.790783+00:00
-- url     : https://prove2.me/submissions/ad47e366-21fa-4301-8b42-cf4a48ded360

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
theorem _root_.solution (hi : Interl lam nu) : lam (Fin.last m) ≤ nu (lastIdx m) := by
  have h := (hi (lastIdx m)).2
  have h1 : (lastIdx m).succ = Fin.last m := by
    apply Fin.ext
    show m - 1 + 1 = m
    have := NeZero.pos m
    omega
  rwa [h1] at h
end Formalism.InvariantFactorPaths.ColumnFamilies
