-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:15.766549+00:00
-- url     : https://prove2.me/submissions/be476649-229b-4194-b38d-9f39d727205b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (p : Fin n) :
    qa_S m (lastIdx n) p = ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and, iff_true]
  rw [Fin.le_def]
  have := b.2
  simp only [lastIdx]
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
