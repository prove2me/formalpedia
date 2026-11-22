-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mn_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:54.067223+00:00
-- url     : https://prove2.me/submissions/c8acf248-b77f-4725-a934-b2b9f0a84d87

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose

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
variable {n : ℕ}
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    qs_mn g J I = Matrix.det (Matrix.of fun a b : Fin h => g (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  subst hI; rw [qs_mn, dif_pos hJ]
end Formalism.InvariantFactorPaths.ColumnFamilies
