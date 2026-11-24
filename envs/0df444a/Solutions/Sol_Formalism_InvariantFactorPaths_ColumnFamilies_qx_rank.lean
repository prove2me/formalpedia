-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:49.258789+00:00
-- url     : https://prove2.me/submissions/ca21678a-01d5-4887-9d12-da8b78ef2ee4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply

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
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}
variable {M M' : GLMod n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) :
    Fintype.card M'.ι = ∑ x : qx_J Str CF, dMu (x.2 : Fin n → ℤ) := by
  rw [Fintype.card_congr e, Fintype.card_prod, CF.rank, sum_mul, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  rw [hd.2.2.2.2.2 _ (CF.dom j)]
  exact (Finset.sum_coe_sort (Str (CF.mu j)) dMu).symm
end Formalism.InvariantFactorPaths.ColumnFamilies
