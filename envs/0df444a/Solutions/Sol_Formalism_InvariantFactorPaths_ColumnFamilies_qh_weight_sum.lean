-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:45.019444+00:00
-- url     : https://prove2.me/submissions/76fe1f15-127e-4357-920e-1c455d0643cb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_le_last
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_count

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
theorem _root_.solution [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun _ : Fin n => mu (lastIdx n)) +
      ∑ c : ↥(TCols mu), (fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0) = mu := by
  funext a
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_coe_sort (TCols mu) (fun c => if a.val < colH mu c then (1 : ℤ) else 0),
    Finset.sum_boole, qh_count hmu a,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmu (qh_le_last a)))]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
