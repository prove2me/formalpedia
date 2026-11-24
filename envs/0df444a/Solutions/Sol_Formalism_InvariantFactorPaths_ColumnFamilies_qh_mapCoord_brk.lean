-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_brk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:23.222888+00:00
-- url     : https://prove2.me/submissions/e1437d7f-0db2-4895-a0df-0adfba8f60f4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_detU
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_minor

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
theorem _root_.solution [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord R (brk mu I) = ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
      ∏ c : ↥(TCols mu), qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q) := by
  first
    | (simp only [brk, TMat]
       rw [map_mul, map_prod, qh_mapCoord_detU]
       congr 1
       refine Finset.prod_congr rfl (fun c _ => ?_)
       exact qh_mapCoord_minor mu c _ _)
    | (simp only [brk, TMat, map_mul, map_prod, qh_mapCoord_detU,
        qh_mapCoord_minor])
end Formalism.InvariantFactorPaths.ColumnFamilies
