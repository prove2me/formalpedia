-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.idxWeight_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.840752+00:00
-- url     : https://prove2.me/submissions/f6e72dc0-59f1-47ca-90ac-65152cb53111

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
private theorem lt_colHeight_iff_lemma {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) (c : ℤ) (m : Fin n) :
    m.val < colHeight μ c ↔ c ≤ μ m := by
  have hmn := m.isLt
  unfold colHeight
  constructor
  · intro hm
    by_contra hc
    have hsub : (univ.filter fun m' : Fin n => c ≤ μ m') ⊆
        univ.filter fun m' : Fin n => m'.val < m.val := by
      intro m' hm'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      by_contra hle
      have := h (Fin.le_iff_val_le_val.mpr (by omega : m.val ≤ m'.val))
      omega
    have h1 := Finset.card_le_card hsub
    rw [card_lt_lemma n m.val (by omega)] at h1
    omega
  · intro hc
    have hsub : (univ.filter fun m' : Fin n => m'.val < m.val + 1) ⊆
        univ.filter fun m' : Fin n => c ≤ μ m' := by
      intro m' hm'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      exact le_trans hc (h (Fin.le_iff_val_le_val.mpr (by omega : m'.val ≤ m.val)))
    have h1 := Finset.card_le_card hsub
    rw [card_lt_lemma n (m.val + 1) (by omega)] at h1
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
theorem _root_.solution {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) : idxWeight (canIdx μ) = μ := by
  funext m
  unfold idxWeight
  have h1 : {c : ℤ | 1 ≤ c ∧ m ∈ canIdx μ c} = Set.Icc 1 (μ m) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hc, hm⟩
      unfold canIdx at hm
      rw [if_pos hc] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      exact ⟨hc, (lt_colHeight_iff_lemma h c m).mp hm⟩
    · rintro ⟨hc, hcm⟩
      refine ⟨hc, ?_⟩
      unfold canIdx
      rw [if_pos hc]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (lt_colHeight_iff_lemma h c m).mpr hcm
  have h2 : {c : ℤ | c ≤ 0 ∧ m ∈ canIdx μ c} = Set.Ioc (μ m) 0 := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨hc, hm⟩
      unfold canIdx at hm
      rw [if_neg (show ¬ (1 ≤ c) by omega)] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      have h3 : ¬ c ≤ μ m := fun h' => absurd ((lt_colHeight_iff_lemma h c m).mpr h') (by omega)
      exact ⟨by omega, hc⟩
    · rintro ⟨hlt, hc⟩
      refine ⟨hc, ?_⟩
      unfold canIdx
      rw [if_neg (show ¬ (1 ≤ c) by omega)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hlt2
      have := (lt_colHeight_iff_lemma h c m).mp (by omega)
      omega
  rw [h1, h2, ← Finset.coe_Icc, ← Finset.coe_Ioc, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Int.card_Icc, Int.card_Ioc]
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
