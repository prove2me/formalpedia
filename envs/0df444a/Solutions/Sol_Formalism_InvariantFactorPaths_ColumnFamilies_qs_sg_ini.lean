-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_sg_ini
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:09.637408+00:00
-- url     : https://prove2.me/submissions/82cd3ce5-09f4-4298-b63c-7a5a7406f5fc

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip

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
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (h : ℕ) (hh : h < n) : qs_sg (qs_ini h) (⟨h, hh⟩ : Fin n) = 1 := by
  have : (qs_ini h : Finset (Fin n)).filter ((⟨h, hh⟩ : Fin n) < ·) = ∅ := by
    ext x; simp only [qs_ini, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and, not_lt]
    intro hx; exact Fin.le_def.2 (by simp only; omega)
  rw [qs_sg, this]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
