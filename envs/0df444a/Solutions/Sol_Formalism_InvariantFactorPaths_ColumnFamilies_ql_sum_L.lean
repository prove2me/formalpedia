-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sum_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:02.467719+00:00
-- url     : https://prove2.me/submissions/1988bae2-3f5d-423c-bc07-2f9d91277f7b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {b : ℕ} (φ : Finset (Fin n) → M) (hφ : ∀ L, L.card ≠ b → φ L = 0) :
    ∑ L : LamIdx n b, φ L.1 = ∑ L, φ L := by
  refine Fintype.sum_of_injective (fun L : LamIdx n b => L.1) Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro L hL
  exact hφ L fun h => hL ⟨⟨L, h⟩, rfl⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
