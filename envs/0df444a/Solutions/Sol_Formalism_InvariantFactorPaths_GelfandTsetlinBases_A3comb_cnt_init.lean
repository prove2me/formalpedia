-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.cnt_init
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.957527+00:00
-- url     : https://prove2.me/submissions/6d3cd39c-c6df-4417-a7d5-7dc85022e5a5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
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
theorem _root_.solution {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = (rowsLt n h).card) :
    ((rowsLt n j).filter fun m => m ∈ J).card ≤ ((rowsLt n j).filter fun m => m ∈ rowsLt n h).card := by
  have e : ((rowsLt n j).filter fun m => m ∈ rowsLt n h) = rowsLt n (min j h) := by
    ext m
    simp [rowsLt, lt_min_iff]
  rw [e, card_rowsLt_lemma]
  have h1 := Finset.card_le_card (Finset.filter_subset (fun m => m ∈ J) (rowsLt n j))
  have h2 : ((rowsLt n j).filter fun m => m ∈ J).card ≤ J.card :=
    Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
  rw [card_rowsLt_lemma] at h1 hJ
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
