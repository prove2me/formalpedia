-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_high_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:25.566803+00:00
-- url     : https://prove2.me/submissions/1a14c3a0-009a-4562-a678-643eb3c8bda5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) : IsHighest M R mu 0 :=
  ⟨Matrix.mulVec_zero _, fun R' _ _ u _ _ => by
    have e : (fun i => algebraMap R R' ((0 : M.ι → R) i)) = 0 := by funext i; simp
    rw [e, Matrix.mulVec_zero]⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
