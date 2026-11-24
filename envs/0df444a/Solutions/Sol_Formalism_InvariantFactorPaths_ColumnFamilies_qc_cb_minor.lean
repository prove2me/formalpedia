-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_cb_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:10.323826+00:00
-- url     : https://prove2.me/submissions/1103a1c9-e04e-47f7-b8c1-67dd3cbd2448

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_cb

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] {n h : ℕ} (x g : Matrix (Fin n) (Fin n) R) (r c : Fin h → Fin n) :
    ((x * g).submatrix r c).det = ∑ S : {S : Finset (Fin n) // S.card = h},
      (x.submatrix r (S.1.orderEmbOfFin S.2)).det * (g.submatrix (S.1.orderEmbOfFin S.2) c).det := by
  have h1 : (x * g).submatrix r c = x.submatrix r id * g.submatrix id c := by
    ext a b; simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [h1, qc_cb]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
