-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ext_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:42.739099+00:00
-- url     : https://prove2.me/submissions/c3cae1ac-859e-43cb-bc2a-6f29a1d69c21

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_high
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_canT


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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) : qs_ext mu (canT mu) c = qs_ini (colH mu c) := by
  unfold qs_ext
  split_ifs with h1 h2
  · ext b; rw [qb_mem_canT]; simp [qs_ini]
  · rw [qs_colH_low hmu h2]; ext b; simp [qs_ini]
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp [qs_ini]
end Formalism.InvariantFactorPaths.ColumnFamilies
