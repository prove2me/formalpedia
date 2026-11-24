-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_can_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:22.464331+00:00
-- url     : https://prove2.me/submissions/b09d75e1-90a4-42db-9b52-f15e3a751ac4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_base_can
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_can_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colH_succ_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_filter_castSucc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_filter_last


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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hi : Interl lam nu) : StdT (qr_j (lam := lam) hi (canT nu)) := by
  intro c hc t
  show ((qr_ext _ (qr_base (canT nu) (c.1 + 1)).1).filter (· ≤ t)).card ≤
    ((qr_ext _ (qr_base (canT nu) c.1).1).filter (· ≤ t)).card
  rw [qr_base_can, qr_base_can]
  induction t using Fin.lastCases with
  | last =>
    rw [qr_filter_last, qr_filter_last, qr_ext_card, qr_ext_card, (qr_can nu _).2, (qr_can nu _).2,
      ← qr_colH_eq hi, ← qr_colH_eq hi]
    exact qc_colH_succ_le lam c
  | cast t =>
    rw [qr_filter_castSucc, qr_filter_castSucc, Finset.card_map, Finset.card_map]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (qr_can_sub c.1))
end Formalism.InvariantFactorPaths.ColumnFamilies
