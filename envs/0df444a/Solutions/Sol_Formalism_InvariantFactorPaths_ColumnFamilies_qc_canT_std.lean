-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_canT_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:58.11452+00:00
-- url     : https://prove2.me/submissions/17ef9843-abf5-4129-9f95-341c2cc9ca94

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colH_succ_le

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le mu c)⟩, rfl⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
