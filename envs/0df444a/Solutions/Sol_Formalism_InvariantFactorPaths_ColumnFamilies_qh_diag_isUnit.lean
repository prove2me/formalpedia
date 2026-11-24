-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_diag_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.256125+00:00
-- url     : https://prove2.me/submissions/bbdb806e-5246-43e0-abdd-4d8cb31baaee

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem

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
theorem _root_.solution {R' : Type} [CommRing R'] (b : GL (Fin n) R')
    (hb : ∀ a c : Fin n, a < c → b.val a c = 0) (a : Fin n) : IsUnit (b.val a a) := by
  have h1 : b.val.det = ∏ i, b.val i i := Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij)
  have h2 : IsUnit (∏ i, b.val i i) := h1 ▸ Matrix.isUnits_det_units b
  exact (IsUnit.prod_univ_iff.1 h2) a
end Formalism.InvariantFactorPaths.ColumnFamilies
