-- Prove2me | solution 1 for BhangaleHypergraph.Main.schrijver_colorable_upper
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:28:43.532874+00:00
-- url     : https://prove2.me/submissions/c97e6d7c-e4de-4b74-abe1-ac6577f98984

import Definitions.Def_BhangaleHypergraph_Main_Restricted

open BhangaleHypergraph.Main

theorem solution (m h : ℕ) (hh : 1 ≤ h) (hm : 2 * h ≤ m) :
    (Schrijver m h).Colorable (m - 2 * h + 2) := by
  classical
  let d := m - 2 * h
  have hd : d + 2 ≤ m := by dsimp [d]; omega
  have hdm : d + 1 < m := by omega
  have hne (A : SchrijverVertex m h) : A.val.Nonempty := by
    rw [← Finset.card_pos, A.property.1]
    exact hh
  let c : SchrijverVertex m h → Fin (d + 2) := fun A =>
    if hA : (A.val.min' (hne A)).val ≤ d then
      ⟨(A.val.min' (hne A)).val, by omega⟩
    else
      ⟨d + 1, by omega⟩
  have hc : ((m - 2 * h + 2) = d + 2) := by rfl
  rw [hc]
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro A B hAB
  have hdis : Disjoint A.val B.val := hAB.2
  by_contra heq
  simp only [c] at heq
  by_cases hA : (A.val.min' (hne A)).val ≤ d
  · have hB : (B.val.min' (hne B)).val ≤ d := by
      by_contra hB
      simp [hA, hB] at heq
      omega
    have hmin : A.val.min' (hne A) = B.val.min' (hne B) := by
      apply Fin.ext
      simpa [hA, hB] using congrArg Fin.val heq
    have hAmem : A.val.min' (hne A) ∈ A.val := Finset.min'_mem _ _
    have hBmem : A.val.min' (hne A) ∈ B.val := hmin ▸ Finset.min'_mem _ _
    exact (Finset.disjoint_left.1 hdis) hAmem hBmem
  · have hB : ¬ (B.val.min' (hne B)).val ≤ d := by
      intro hB
      simp [hA, hB] at heq
      omega
    have hAsub : A.val ⊆ Finset.Ici (⟨d + 1, hdm⟩ : Fin m) := by
      intro x hx
      rw [Finset.mem_Ici]
      have hle := Finset.min'_le A.val x hx
      change d + 1 ≤ x.val
      have hminle : (A.val.min' (hne A)).val ≤ x.val := hle
      omega
    have hBsub : B.val ⊆ Finset.Ici (⟨d + 1, hdm⟩ : Fin m) := by
      intro x hx
      rw [Finset.mem_Ici]
      have hle := Finset.min'_le B.val x hx
      change d + 1 ≤ x.val
      have hminle : (B.val.min' (hne B)).val ≤ x.val := hle
      omega
    have hunion : (A.val ∪ B.val).card = 2 * h := by
      rw [Finset.card_union_of_disjoint hdis, A.property.1, B.property.1]
      omega
    have hsub : A.val ∪ B.val ⊆ Finset.Ici (⟨d + 1, hdm⟩ : Fin m) :=
      Finset.union_subset hAsub hBsub
    have hcard := Finset.card_le_card hsub
    rw [hunion, Fin.card_Ici] at hcard
    dsimp at hcard
    omega
