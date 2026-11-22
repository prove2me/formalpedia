-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.isIndex_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:21.211197+00:00
-- url     : https://prove2.me/submissions/d333d0b5-81d9-463f-ad7f-ab74f0f3d8d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le

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
namespace A1
section Top
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
end Top
section Col
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
end Col
private theorem compl_seg_lemma_8 {n : ℕ} (k : ℕ) :
    (univ.filter fun m : Fin n => m.val < k)ᶜ = univ.filter fun m : Fin n => k ≤ m.val := by
  ext x
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h <;> omega
private theorem card_seg_lemma_9 {n : ℕ} (k : ℕ) (hk : k ≤ n) : (univ.filter fun m : Fin n => m.val < k).card = k := by
  have e : (univ.filter fun m : Fin n => m.val < k).map Fin.valEmbedding = range k := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]
end A1
namespace A1
end A1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n : ℕ} (μN : Fin n → ℤ) : IsIndex μN (canIdx μN) := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex
  intro c
  have hle := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_le μN c
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
  split_ifs
  · exact card_seg_lemma_9 _ hle
  · rw [← compl_seg_lemma_8, Finset.card_compl, Fintype.card_fin, card_seg_lemma_9 _ hle]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
