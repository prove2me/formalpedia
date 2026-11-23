-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_Slt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:49.16284+00:00
-- url     : https://prove2.me/submissions/bbdeaf2b-c46e-4efe-b485-7e0d6051f76c

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
theorem _root_.solution {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) :
    (∑ b : Fin n with b < a, m (b, p)) = 0 ∨ ∃ b, b < a ∧ (∑ b : Fin n with b < a, m (b, p)) = qa_S m b p := by
  obtain ⟨a, ha⟩ := a
  cases a with
  | zero =>
    left
    apply Finset.sum_eq_zero
    intro b hb
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hb
    omega
  | succ k =>
    right
    refine ⟨⟨k, by omega⟩, by simp [Fin.lt_def], ?_⟩
    unfold qa_S
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def, Fin.le_def]
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
