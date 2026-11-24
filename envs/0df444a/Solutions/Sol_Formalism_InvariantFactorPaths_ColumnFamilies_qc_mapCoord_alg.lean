-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_mapCoord_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.443505+00:00
-- url     : https://prove2.me/submissions/b04a4c61-0bbf-4d20-b682-3ae14de919d6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt

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
theorem _root_.solution {n : ℕ} (F : Type) [CommRing F] (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) P) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) P) :=
  IsLocalization.Away.lift_eq _ _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
