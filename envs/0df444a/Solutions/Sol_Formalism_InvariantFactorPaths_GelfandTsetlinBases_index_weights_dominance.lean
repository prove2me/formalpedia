-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.index_weights_dominance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:15.730347+00:00
-- url     : https://prove2.me/submissions/b96db6d9-2a4d-4834-8882-ae46bd04efee

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_idx_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_exists_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_sum_idxWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_idxWeight_can
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_can_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_can_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_col_le
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_col_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A3comb
end A3comb
namespace A3comb
private theorem card_lt_lemma (n k : ℕ) (hk : k ≤ n) :
    (univ.filter fun m : Fin n => m.val < k).card = k := by
  have e : (univ.filter fun m : Fin n => m.val < k).map Fin.valEmbedding = range k := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]
private theorem card_rowsLt_lemma (n k : ℕ) : (rowsLt n k).card = min k n := by
  unfold rowsLt
  rcases le_total k n with hk | hk
  · rw [card_lt_lemma n k hk]
    omega
  · rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    · omega
    · intro m _
      have := m.isLt
      omega
end A3comb
namespace A3comb
end A3comb
namespace A3comb
end A3comb
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : IndexWeightsDominance := by
  intro n μ I hμ hI
  obtain ⟨M, hM⟩ := exists_bound μ
  have hS : ∀ c, c ∉ Finset.Icc (-M) M → I c = ∅ := fun c hc => idx_empty hI M hM c hc
  have hle : ∀ c, colHeight μ c ≤ n := fun c => by
    unfold colHeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hcan : IsIndex μ (canIdx μ) := by
    intro c
    have := hle c
    by_cases hc : 1 ≤ c
    · rw [if_pos hc, can_pos μ hc, card_rowsLt_lemma]
      omega
    · rw [if_neg hc, can_neg μ hc, Finset.card_compl, Fintype.card_fin, card_rowsLt_lemma]
      omega
  have hS' : ∀ c, c ∉ Finset.Icc (-M) M → canIdx μ c = ∅ := fun c hc => idx_empty hcan M hM c hc
  have hsum : ∀ j, ∑ m ∈ rowsLt n j, idxWeight I m ≤ ∑ m ∈ rowsLt n j, μ m := by
    intro j
    rw [show (∑ m ∈ rowsLt n j, μ m) = ∑ m ∈ rowsLt n j, idxWeight (canIdx μ) m by
      rw [idxWeight_can hμ], sum_idxWeight I _ hS, sum_idxWeight (canIdx μ) _ hS']
    exact Finset.sum_le_sum fun c _ => col_le hI c j
  have e : (Finset.univ : Finset (Fin n)) = rowsLt n n := by
    ext m
    simp [rowsLt]
  have g : ∀ X : Finset (Fin n), ((rowsLt n n).filter fun m => m ∈ X) = X := by
    intro X
    rw [← e]
    ext m
    simp
  have htot : ∑ m, idxWeight I m = ∑ m, μ m := by
    rw [e, show (∑ m ∈ rowsLt n n, μ m) = ∑ m ∈ rowsLt n n, idxWeight (canIdx μ) m by
      rw [idxWeight_can hμ], sum_idxWeight I _ hS, sum_idxWeight (canIdx μ) _ hS']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [g, g, hI c, hcan c]
  refine ⟨?_, fun hw => ?_⟩
  · unfold DomLe
    exact ⟨htot, fun j => hsum j⟩
  funext c
  by_cases hcS : c ∈ Finset.Icc (-M) M
  · apply col_eq hI c
    have hsum0 : ∑ c' ∈ Finset.Icc (-M) M, ((if 1 ≤ c' then (1 : ℤ) else -1) *
        (((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c').card : ℤ) -
        (if 1 ≤ c' then (1 : ℤ) else -1) *
        (((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c').card : ℤ)) = 0 := by
      rw [Finset.sum_sub_distrib, ← sum_idxWeight I _ hS, ← sum_idxWeight (canIdx μ) _ hS',
        idxWeight_can hμ, hw, sub_self]
    rw [Finset.sum_eq_zero_iff_of_nonpos
      (fun c' _ => sub_nonpos.mpr (col_le hI c' (colHeight μ c)))] at hsum0
    have h0 := hsum0 c hcS
    have h1 : (((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card : ℤ) =
        (((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card : ℤ) := by
      split_ifs at h0 <;> linarith
    exact_mod_cast h1
  · rw [hS c hcS, hS' c hcS]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
