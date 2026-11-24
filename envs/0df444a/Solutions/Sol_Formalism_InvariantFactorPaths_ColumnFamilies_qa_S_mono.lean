-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_S_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:15.85722+00:00
-- url     : https://prove2.me/submissions/24398ed6-ded1-4c2e-922b-e62c6cc1133a

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
theorem _root_.solution {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (p : Fin n) {a a' : Fin n} (h : a ≤ a') :
    qa_S m a p ≤ qa_S m a' p := by
  unfold qa_S
  apply Finset.sum_le_sum_of_subset
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact hb.trans h
end Formalism.InvariantFactorPaths.ColumnFamilies
