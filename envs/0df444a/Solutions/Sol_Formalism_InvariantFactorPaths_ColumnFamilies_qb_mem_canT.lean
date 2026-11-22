-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_mem_canT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:41.206893+00:00
-- url     : https://prove2.me/submissions/7a81c395-6099-4f9e-951d-605f6cea1bf0

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

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
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (c : ↥(TCols mu)) (b : Fin n) :
    b ∈ (canT mu c).1 ↔ b.val < colH mu c := by
  simp only [canT, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨b.val, h⟩, by ext; rfl⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
