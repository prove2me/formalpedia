-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_det_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:40.773521+00:00
-- url     : https://prove2.me/submissions/6f590b55-e133-4421-9d17-96a68273956d

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) : Matrix.GeneralLinearGroup.det u = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (fun a b hab => h2 a b hab)]
  simp [h1]
end Formalism.InvariantFactorPaths.ColumnFamilies
