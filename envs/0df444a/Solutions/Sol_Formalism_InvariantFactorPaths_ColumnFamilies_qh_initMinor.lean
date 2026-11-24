-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_initMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:23.707982+00:00
-- url     : https://prove2.me/submissions/1e4ce616-db49-45b9-bb13-211aac0d8d0a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
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
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [NeZero n] {s : ℕ} (I : Fin s → Fin n) (hs : s ≤ n) :
    algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.initMinor R I hs)) =
      qhM R s (fun q => if h : q < s then I ⟨q, h⟩ else 0) := by
  unfold qhM qhN Formalism.GradedWeylDivisibility.initMinor
  rw [dif_pos hs]
  congr 1
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp [genMat, AlgHom.mapMatrix_apply, Matrix.transpose_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
