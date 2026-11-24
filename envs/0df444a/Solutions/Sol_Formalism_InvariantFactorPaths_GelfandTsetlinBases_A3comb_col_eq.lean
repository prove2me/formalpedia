-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.col_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.826257+00:00
-- url     : https://prove2.me/submissions/919a5634-ac7d-43f4-8ff5-62c65fa766cc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_can_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_can_neg
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ)
    (h : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card =
      ((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card) : I c = canIdx μ c := by
  have hle : colHeight μ c ≤ n := by
    unfold colHeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have key := hI c
  by_cases hc : 1 ≤ c
  · rw [if_pos hc] at key
    rw [can_pos μ hc] at h ⊢
    have f1 : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c) ⊆ I c :=
      fun x hx => (Finset.mem_filter.mp hx).2
    have f2 : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c) ⊆ rowsLt n (colHeight μ c) :=
      Finset.filter_subset _ _
    have e : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ rowsLt n (colHeight μ c)) =
        rowsLt n (colHeight μ c) :=
      Finset.filter_true_of_mem fun x hx => hx
    rw [e, card_rowsLt_lemma] at h
    have g1 := Finset.eq_of_subset_of_card_le f1 (by omega)
    have g2 := Finset.eq_of_subset_of_card_le f2 (by rw [card_rowsLt_lemma]; omega)
    exact g1.symm.trans g2
  · rw [if_neg hc] at key
    rw [can_neg μ hc] at h ⊢
    have e : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ (rowsLt n (colHeight μ c))ᶜ) = ∅ := by
      ext m
      simp
    rw [e, Finset.card_empty] at h
    have hsub : I c ⊆ (rowsLt n (colHeight μ c))ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxR
      have hmem : x ∈ (rowsLt n (colHeight μ c)).filter fun m => m ∈ I c :=
        Finset.mem_filter.mpr ⟨hxR, hx⟩
      rw [Finset.card_eq_zero.mp h] at hmem
      simp at hmem
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_compl, Fintype.card_fin, card_rowsLt_lemma, key]; omega)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
