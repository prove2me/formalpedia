-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ext_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.010019+00:00
-- url     : https://prove2.me/submissions/37470dbb-16de-44ad-8595-38c5ab94e49a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_high

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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (F : ℤ → Finset (Fin n))
    (hF : ∀ c, (F c).card = colH mu c) : qs_ext mu (qs_res mu F hF) = F := by
  funext c
  unfold qs_ext
  split_ifs with h1 h2
  · rfl
  · symm; apply Finset.eq_univ_of_card; rw [hF, qs_colH_low hmu h2]; simp
  · symm; rw [← Finset.card_eq_zero, hF, qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]
end Formalism.InvariantFactorPaths.ColumnFamilies
