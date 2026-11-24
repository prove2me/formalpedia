-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_of_cum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:49.645868+00:00
-- url     : https://prove2.me/submissions/7158a045-5b76-4cde-bda3-d59b79d14bed

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Slt
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
theorem _root_.solution {n : ℕ} (m m' : Fin n × Fin n →₀ ℕ) (h : ∀ a p, qa_S m a p = qa_S m' a p) : m = m' := by
  ext ⟨a, p⟩
  have hsplit : ∀ (m : Fin n × Fin n →₀ ℕ), qa_S m a p = m (a, p) + ∑ b : Fin n with b < a, m (b, p) := by
    intro m
    unfold qa_S
    have : (univ.filter fun b : Fin n => b ≤ a) = insert a (univ.filter fun b : Fin n => b < a) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      exact le_iff_eq_or_lt
    rw [this, Finset.sum_insert (by simp)]
  have h1 := h a p
  rw [hsplit m, hsplit m'] at h1
  rcases qa_Slt m a p with h0 | ⟨b, hb, h2⟩
  · rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · omega
    ·
      have h3 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b' p
      omega
  · have h3 : qa_S m' b p ≤ ∑ b : Fin n with b < a, m' (b, p) := by
      unfold qa_S
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact lt_of_le_of_lt hx hb
    rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · have := h b p
      omega
    · have h4 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b p
      have := h b' p
      omega
end Formalism.InvariantFactorPaths.ColumnFamilies
