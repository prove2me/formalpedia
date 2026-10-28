-- Prove2me | solution 1 for CycleLengthsExp.BetaGraph.large_set_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:38:53.33998+00:00
-- url     : https://prove2.me/submissions/29c5be1e-58e6-4d9c-9fc0-fa1b4862e40b

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

open CycleLengthsExp.BetaGraph in
theorem solution (β : ℝ) (hβ : 0 < β) (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : IsBetaGraph β G) (S : Set (Fin n)) (hS : (1 - β) * n ≤ S.ncard)
    (hSexp : ∀ U ⊆ S, (U.ncard : ℝ) ≤ β * n →
      (1 - 3 * β) / (2 * β) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard) :
    (∀ U ⊆ S, β * n ≤ U.ncard →
        ((S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))).ncard : ℝ) < β * n) ∧
    (∀ U ⊆ S, β * n ≤ U.ncard → (U.ncard : ℝ) ≤ 2 * β * n →
        (1 - 4 * β) * n < (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard) := by
  have part1 : ∀ U ⊆ S, β * n ≤ U.ncard →
      ((S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))).ncard : ℝ) < β * n := by
    intro U _ hU
    by_contra hcon
    push_neg at hcon
    have hdisj : Disjoint U (S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))) := by
      rw [Set.disjoint_left]
      intro x hxU hxW
      exact hxW.2 (Or.inl hxU)
    have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
    obtain ⟨a, ha, b, hb, hab⟩ := hG U _ hdisj (by rw [hcard]; exact hU) (by rw [hcard]; exact hcon)
    have hbU : b ∉ U := fun h => hb.2 (Or.inl h)
    exact hb.2 (Or.inr ⟨⟨hbU, a, ha, hab⟩, hb.1⟩)
  refine ⟨part1, ?_⟩
  intro U hUS hU hU2
  have hW := part1 U hUS hU
  have hsub : S ⊆ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S)) ∪
      (S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))) := by
    intro x hx
    by_cases h : x ∈ U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S)
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_union_le (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))
    (S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S)))
  have h3 := Set.ncard_union_le U (CycleLengthsExp.WellSpread.extNbhd G U ∩ S)
  have h4 : (S.ncard : ℝ) ≤ U.ncard + (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard +
      (S \ (U ∪ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S))).ncard := by
    exact_mod_cast h1.trans (h2.trans (by omega))
  nlinarith
