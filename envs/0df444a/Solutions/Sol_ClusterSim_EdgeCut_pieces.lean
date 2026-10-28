-- Prove2me | solution 1 for ClusterSim.EdgeCut.pieces
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:40:54.386598+00:00
-- url     : https://prove2.me/submissions/18627a4d-edc6-4542-a999-962c977a0397

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Clustering

open ClusterSim.EdgeCut in
theorem solution {G : TensorNetwork} {r K d : ℕ} (P : Clustering G r) (hP : P.IsClustered K d)
    (s : P.Ecut → Fin 8) :
    (P.cutClustering s).Ecut = ∅ ∧ ∀ i, (P.cutClustering s).qubits i ≤ d := by
  classical
  set G' := cut G P.Ecut s with hG'
  set P' := P.cutClustering s with hP'
  have hmemE : ∀ e, e ∈ P.Ecut ↔ G.tgt e ≠ P.obs ∧ P.cl (G.src e) ≠ P.cl (G.tgt e) := by
    intro e; unfold Clustering.Ecut; rw [Finset.mem_filter]; simp
  have htgtL : ∀ e, G'.tgt (Sum.inl e) =
      if h : e ∈ P.Ecut then Sum.inr (Sum.inl ⟨e, h⟩) else Sum.inl (G.tgt e) := fun e => rfl
  have htgtR : ∀ e, G'.tgt (Sum.inr e) = Sum.inl (G.tgt e.1) := fun e => rfl
  have hsrcL : ∀ e, G'.src (Sum.inl e) = Sum.inl (G.src e) := fun e => rfl
  have hsrcR : ∀ e, G'.src (Sum.inr e) = Sum.inr (Sum.inr e) := fun e => rfl
  have hclL : ∀ v, P'.cl (Sum.inl v) = P.cl v := fun v => rfl
  have hclO : ∀ e, P'.cl (Sum.inr (Sum.inl e)) = P.cl (G.src e.1) := fun e => rfl
  have hclS : ∀ e, P'.cl (Sum.inr (Sum.inr e)) = P.cl (G.tgt e.1) := fun e => rfl
  have hobs : P'.obs = Sum.inl P.obs := rfl
  -- no edge of the cut network is cut
  have hnocut : ∀ e' : G'.E, ¬ (G'.tgt e' ≠ P'.obs ∧ P'.cl (G'.src e') ≠ P'.cl (G'.tgt e')) := by
    rintro (e | e) ⟨h1, h2⟩
    · rw [hsrcL, hclL, htgtL] at h2
      rw [htgtL, hobs] at h1
      by_cases hc : e ∈ P.Ecut
      · rw [dif_pos hc, hclO] at h2
        exact h2 rfl
      · rw [dif_neg hc, hclL] at h2
        rw [dif_neg hc] at h1
        have h3 : G.tgt e ≠ P.obs := fun h => h1 (by rw [h])
        exact hc ((hmemE e).mpr ⟨h3, h2⟩)
    · rw [hsrcR, hclS, htgtR, hclL] at h2
      exact h2 rfl
  constructor
  · show Finset.univ.filter (fun e => G'.tgt e ≠ P'.obs ∧ P'.cl (G'.src e) ≠ P'.cl (G'.tgt e)) = ∅
    rw [Finset.filter_eq_empty_iff]
    intro e' _
    exact hnocut e'
  · intro i
    have hq := hP.2 i
    unfold Clustering.qubits at hq ⊢
    -- second count vanishes
    have h2 : (Finset.univ.filter fun e' : G'.E => G'.tgt e' ≠ P'.obs ∧ P'.cl (G'.tgt e') = i ∧
        P'.cl (G'.src e') ≠ i).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro e' - ⟨h1, h2, h3⟩
      exact hnocut e' ⟨h1, by rw [h2]; exact h3⟩
    have key : ∀ (p : G.V ⊕ (P.Ecut ⊕ P.Ecut) → Prop) {inst : DecidablePred p}
        (A : Finset G.V) (B C : Finset P.Ecut),
        (∀ v, p (Sum.inl v) ↔ v ∈ A) → (∀ c, p (Sum.inr (Sum.inl c)) ↔ c ∈ B) →
        (∀ c, p (Sum.inr (Sum.inr c)) ↔ c ∈ C) →
        (Finset.univ.filter p).card = A.card + (B.card + C.card) := by
      intro p inst A B C hA hB hC
      rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
      have e1 : ∀ (X : Type) [Fintype X] [DecidableEq X] (q : X → Prop) [DecidablePred q]
          (S : Finset X), (∀ x, q x ↔ x ∈ S) → (∑ x, if q x then 1 else 0) = S.card := by
        intro X _ _ q _ S hS
        rw [← Finset.card_filter]
        congr 1
        ext x
        simp [hS]
      rw [e1 _ _ A hA, e1 _ _ B hB, e1 _ _ C hC]
    have hin : ∀ v : G.V, (∀ e' : G'.E, G'.tgt e' ≠ Sum.inl v) ↔ ∀ e : G.E, G.tgt e ≠ v := by
      intro v
      constructor
      · intro h e he
        by_cases hc : e ∈ P.Ecut
        · apply h (Sum.inr ⟨e, hc⟩); rw [htgtR, he]
        · apply h (Sum.inl e); rw [htgtL, dif_neg hc, he]
      · rintro h (e | e) he
        · rw [htgtL] at he
          by_cases hc : e ∈ P.Ecut
          · rw [dif_pos hc] at he; exact Sum.inr_ne_inl he
          · rw [dif_neg hc] at he; exact h e (Sum.inl_injective he)
        · rw [htgtR] at he; exact h e.1 (Sum.inl_injective he)
    have hC : (Finset.univ.filter (fun c : P.Ecut => P.cl (G.tgt c.1) = i)).card =
        (Finset.univ.filter fun e => G.tgt e ≠ P.obs ∧ P.cl (G.tgt e) = i ∧
          P.cl (G.src e) ≠ i).card := by
      rw [Finset.card_filter, Finset.card_filter]
      rw [Finset.sum_coe_sort P.Ecut (fun e => if P.cl (G.tgt e) = i then 1 else 0)]
      rw [← Finset.card_filter, ← Finset.card_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmemE]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, by rw [← h3]; exact h2⟩
      · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, by rw [h3]; exact h2⟩, h3⟩
    rw [h2, add_zero]
    refine le_trans (le_of_eq (key _
      (Finset.univ.filter (fun v => v ≠ P.obs ∧ P.cl v = i ∧ ∀ e, G.tgt e ≠ v)) ∅
      (Finset.univ.filter (fun c : P.Ecut => P.cl (G.tgt c.1) = i)) ?_ ?_ ?_)) ?_
    · intro v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun h => h1 (by rw [h]; rfl), h2, (hin v).mp h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun h => h1 (Sum.inl_injective h), h2, (hin v).mpr h3⟩
    · intro c
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨-, -, h⟩
      apply h (Sum.inl c.1)
      rw [htgtL, dif_pos c.2]
    · intro c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h, -⟩; exact h
      · intro h
        refine ⟨fun h' => Sum.inr_ne_inl h', h, ?_⟩
        rintro (e | e) he
        · rw [htgtL] at he
          by_cases hc : e ∈ P.Ecut
          · rw [dif_pos hc] at he
            exact Sum.inl_ne_inr (Sum.inr_injective he)
          · rw [dif_neg hc] at he; exact Sum.inl_ne_inr he
        · rw [htgtR] at he; exact Sum.inl_ne_inr he
    · rw [Finset.card_empty, zero_add, hC]
      exact hq
