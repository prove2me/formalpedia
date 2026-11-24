-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:51:02.13005+00:00
-- url     : https://prove2.me/submissions/10c50eb4-4fa6-4652-bf2b-b9cc0ad8c0e4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sW_isUnit
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_isUnit


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
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {N : ℕ} (k i : Fin N → Finset (Fin n)) (hk : ∀ j, k j ⊆ i j)
    (hd : ∀ j j', j ≠ j' → Disjoint (i j \ k j) (i j' \ k j')) :
    IsUnit (ql_P R k (ql_U N fun j => i j \ k j) i) := by
  have h0 : ∀ D : Fin N → Finset (Fin n), D ≠ (fun j => i j \ k j) →
      (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D (ql_U N fun j => i j \ k j) = 0 := by
    intro D hD
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hD
    rw [prod_eq_zero (mem_univ j), zero_mul]
    rw [ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hdis
      apply hj
      rw [← h, union_sdiff_cancel_left hdis]
    · rfl
  rw [ql_P, sum_eq_single _ (fun D _ hD => h0 D hD) (fun h => absurd (mem_univ _) h)]
  refine IsUnit.mul ?_ ?_
  · refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ?_
    rw [ql_w, if_pos (union_sdiff_of_subset (hk j))]
    exact ql_s_isUnit disjoint_sdiff
  · rw [wedgeCoeff, if_pos rfl]
    exact ql_sW_isUnit N _ hd
end Formalism.InvariantFactorPaths.ColumnFamilies
