-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_detU_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:50.498151+00:00
-- url     : https://prove2.me/submissions/d504d728-6c2b-4589-b8bb-f7571b026ec2

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_detU

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
theorem _root_.solution {R : Type} [CommRing R] (g : GL (Fin n) R) (u : Rˣ) (hu : (u : R) = g.val.det) (z : ℤ) :
    evGL g ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((u ^ z : Rˣ) : R) := by
  have : Units.map (evGL g : GLCoord ℤ n →* R) (detU n) = u := Units.ext (by
    rw [Units.coe_map, hu]; exact qb_evGL_detU g)
  rw [← this, ← map_zpow, Units.coe_map]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
