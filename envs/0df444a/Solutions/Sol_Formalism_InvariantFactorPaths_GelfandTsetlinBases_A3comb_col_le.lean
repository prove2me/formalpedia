-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.col_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:18.983886+00:00
-- url     : https://prove2.me/submissions/9547d18e-36e0-4dd5-8da1-73c0b3ac86d7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_cnt_init
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_card_filter_lt_le_alt
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
theorem _root_.solution {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ) (j : ℕ) :
    (if 1 ≤ c then (1 : ℤ) else -1) * (((rowsLt n j).filter fun m => m ∈ I c).card : ℤ) ≤
      (if 1 ≤ c then (1 : ℤ) else -1) * (((rowsLt n j).filter fun m => m ∈ canIdx μ c).card : ℤ) := by
  have hle : colHeight μ c ≤ n := by
    unfold colHeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have key := hI c
  by_cases hc : 1 ≤ c
  · rw [if_pos hc] at key ⊢
    rw [can_pos μ hc]
    have := cnt_init (I c) (colHeight μ c) j (by rw [key, card_rowsLt_lemma]; omega)
    simp only [one_mul]
    exact_mod_cast this
  · rw [if_neg hc] at key ⊢
    rw [can_neg μ hc]
    have := card_filter_lt_le_alt (I c) (colHeight μ c) j
      (by rw [key, Finset.card_compl, Fintype.card_fin, card_rowsLt_lemma]; omega)
    have h' : (((rowsLt n j).filter fun m => m ∈ (rowsLt n (colHeight μ c))ᶜ).card : ℤ) ≤
        (((rowsLt n j).filter fun m => m ∈ I c).card : ℤ) := by
      exact_mod_cast this
    linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
