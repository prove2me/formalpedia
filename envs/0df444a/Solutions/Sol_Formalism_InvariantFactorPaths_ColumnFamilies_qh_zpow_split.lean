-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_zpow_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.101273+00:00
-- url     : https://prove2.me/submissions/3f699570-83af-491c-a34f-2b8ee742c886

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
theorem _root_.solution {G : Type*} [CommGroup G] (u : G) (z : ℤ) : u ^ z * u ^ (-z).toNat = u ^ z.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
  congr 1
  have := Int.toNat_sub_toNat_neg z
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
