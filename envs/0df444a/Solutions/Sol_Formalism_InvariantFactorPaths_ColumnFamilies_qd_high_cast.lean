-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_high_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:35:59.683854+00:00
-- url     : https://prove2.me/submissions/302083f3-f7a2-4098-bc8e-9ade83d6c782

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M : GLMod n) (mu : Fin n → ℤ) (x : M.ι → ℤ) (hx : IsHighest M ℤ mu x) :
    IsHighest M ℚ mu (fun i => (x i : ℚ)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → ℚ) (congrFun hx.1 i)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro R' _ _ u h1 h2
    have := hx.2 R' u h1 h2
    simpa using this
end Formalism.InvariantFactorPaths.ColumnFamilies
