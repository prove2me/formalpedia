-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_detU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:50.462801+00:00
-- url     : https://prove2.me/submissions/ba614e4b-3f2a-4b16-a1fa-a9bdae874cea

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_algebraMap

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (g : GL (Fin n) R) : evGL g (detU n : GLCoord ℤ n) = g.val.det := by
  have : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ (GLCoord ℤ n) (genMat ℤ n).det := rfl
  rw [this, qb_evGL_algebraMap, RingHom.map_det, genMat_map_eval]
end Formalism.InvariantFactorPaths.ColumnFamilies
