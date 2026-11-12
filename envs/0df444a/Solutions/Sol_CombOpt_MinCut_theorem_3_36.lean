-- Prove2me | solution 1 for CombOpt.MinCut.theorem_3_36
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T20:59:10.966425+00:00
-- url     : https://prove2.me/submissions/b09016ea-67b1-4aa5-86a2-a2c16cae9484

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_IsMinCut
import Definitions.Def_CombOpt_MinCut_CapGraph_IsLegalOrdering

set_option autoImplicit false

namespace CombOpt.MinCut.LegalOrd

open Classical

variable {V E : Type*} [Fintype E]

set_option linter.unusedSectionVars false

lemma uSum_mono (G : CapGraph V E) (hu : ∀ e, 0 ≤ G.u e) {A B : Finset E} (h : A ⊆ B) :
    G.uSum A ≤ G.uSum B :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => hu e)

lemma step (G : CapGraph V E) (hu : ∀ e, 0 ≤ G.u e) {X X' C D : Finset E}
    (h1 : G.uSum X ≤ G.uSum D) (h2 : D ⊆ C) (h3 : X' \ X ⊆ C \ D) : G.uSum X' ≤ G.uSum C := by
  have e1 : G.uSum X' = G.uSum (X' \ (X' ∩ X)) + G.uSum (X' ∩ X) := by
    unfold CapGraph.uSum; exact (Finset.sum_sdiff Finset.inter_subset_left).symm
  have e2 : G.uSum C = G.uSum (C \ D) + G.uSum D := by
    unfold CapGraph.uSum; exact (Finset.sum_sdiff h2).symm
  have i1 := uSum_mono G hu (Finset.inter_subset_right : X' ∩ X ⊆ X)
  have i2 : G.uSum (X' \ (X' ∩ X)) ≤ G.uSum (C \ D) := uSum_mono G hu (fun e he => h3 (by
    simp only [Finset.mem_sdiff, Finset.mem_inter] at he ⊢; tauto))
  linarith

lemma ends_rep {n : ℕ} (σ : Fin n ≃ V) (G : CapGraph V E) (e : E) :
    ∃ a b : Fin n, G.ends e = s(σ a, σ b) := by
  have : ∀ z : Sym2 V, ∃ a b : Fin n, z = s(σ a, σ b) := by
    intro z
    refine Sym2.ind (fun x y => ?_) z
    exact ⟨σ.symm x, σ.symm y, by simp⟩
  exact this _

/-- The prefix `{σ k : k < i}`. -/
noncomputable def pre {n : ℕ} (σ : Fin n ≃ V) (i : ℕ) : Finset V :=
  (Finset.univ.filter (fun k : Fin n => k.val < i)).map σ.toEmbedding

@[simp] lemma mem_pre {n : ℕ} (σ : Fin n ≃ V) (i : ℕ) (a : Fin n) :
    σ a ∈ pre σ i ↔ a.val < i := by
  simp [pre]

lemma pre_eq {n : ℕ} (σ : Fin n ≃ V) (i : Fin n) :
    (Finset.univ.filter (fun k : Fin n => k < i)).map σ.toEmbedding = pre σ i.val := by
  ext x
  obtain ⟨a, rfl⟩ := σ.surjective x
  simp [pre]

lemma mem_delta_iff (G : CapGraph V E) (T : Finset V) (e : E) (x y : V)
    (h : G.ends e = s(x, y)) :
    e ∈ G.delta T ↔ ((x ∈ T ∨ y ∈ T) ∧ (x ∉ T ∨ y ∉ T)) := by
  simp [CapGraph.delta, h, Sym2.mem_iff]

/-- The cut edges of `S` with all ends in `pre σ i ∪ {σ j}`. -/
noncomputable def C {n : ℕ} (G : CapGraph V E) (σ : Fin n ≃ V) (S : Finset V) (i : ℕ)
    (j : Fin n) : Finset E :=
  Finset.univ.filter (fun e => e ∈ G.delta S ∧ ∀ a ∈ G.ends e, (σ.symm a).val < i ∨ a = σ j)

/-- An edge of `δ(V_{i+1}) ∩ δ(v_j)` not in `δ(V_i) ∩ δ(v_j)` joins `v_i` and `v_j`. -/
lemma new_edge {n : ℕ} (G : CapGraph V E) (σ : Fin n ≃ V) (i : ℕ) (j : Fin n)
    (hij : i + 1 ≤ j.val) (e : E)
    (h1 : e ∈ G.delta (pre σ (i + 1)) ∩ G.delta {σ j})
    (h2 : e ∉ G.delta (pre σ i) ∩ G.delta {σ j}) :
    G.ends e = s(σ ⟨i, by have := j.isLt; omega⟩, σ j) := by
  obtain ⟨a, b, hab⟩ := ends_rep σ G e
  rw [Finset.mem_inter, mem_delta_iff G _ e _ _ hab, mem_delta_iff G _ e _ _ hab] at h1
  rw [Finset.mem_inter, mem_delta_iff G _ e _ _ hab, mem_delta_iff G _ e _ _ hab] at h2
  simp only [mem_pre, Finset.mem_singleton, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff] at h1 h2
  have key : (a.val = i ∧ b.val = j.val) ∨ (b.val = i ∧ a.val = j.val) := by omega
  rcases key with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · have ha' : a = ⟨i, by have := j.isLt; omega⟩ := Fin.ext ha
    have hb' : b = j := Fin.ext hb
    rw [hab, ha', hb']
  · have hb' : b = ⟨i, by have := j.isLt; omega⟩ := Fin.ext hb
    have ha' : a = j := Fin.ext ha
    rw [hab, ha', hb', Sym2.eq_swap]

lemma new_mem {n : ℕ} (G : CapGraph V E) (σ : Fin n ≃ V) (S : Finset V) (i : ℕ) (j : Fin n)
    (hij : i + 1 ≤ j.val) (hS : ¬ (σ j ∈ S ↔ σ ⟨i, by have := j.isLt; omega⟩ ∈ S)) (e : E)
    (he : G.ends e = s(σ ⟨i, by have := j.isLt; omega⟩, σ j)) :
    e ∈ C G σ S (i + 1) j ∧ e ∉ C G σ S i j ∧
      e ∉ C G σ S i ⟨i, by have := j.isLt; omega⟩ := by
  have hne : (⟨i, by have := j.isLt; omega⟩ : Fin n) ≠ j := by
    intro h; rw [Fin.ext_iff] at h; simp at h; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, mem_delta_iff G S e _ _ he, he,
      Sym2.mem_iff]
    refine ⟨by tauto, ?_⟩
    rintro x (rfl | rfl)
    · left; simp
    · right; rfl
  · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, he, Sym2.mem_iff, not_and]
    intro _ h
    rcases h _ (Or.inl rfl) with h | h
    · simp at h
    · exact hne (σ.injective h)
  · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, he, Sym2.mem_iff, not_and]
    intro _ h
    rcases h _ (Or.inr rfl) with h | h
    · simp at h; omega
    · exact hne (σ.injective h).symm

lemma key (G : CapGraph V E) (hu : ∀ e, 0 ≤ G.u e) {n : ℕ} (σ : Fin n ≃ V)
    (hσ : G.IsLegalOrdering σ) (S : Finset V) :
    ∀ m : ℕ, ∀ (j : Fin n) (hj : m + 1 ≤ j.val),
      ¬ (σ j ∈ S ↔ σ ⟨m, by have := j.isLt; omega⟩ ∈ S) →
      G.uSum (G.delta (pre σ (m + 1)) ∩ G.delta {σ j}) ≤ G.uSum (C G σ S (m + 1) j) := by
  intro m
  induction m with
  | zero =>
    intro j hj hS
    apply uSum_mono G hu
    intro e he
    have h2 : e ∉ G.delta (pre σ 0) ∩ G.delta {σ j} := by
      intro h
      obtain ⟨a, b, hab⟩ := ends_rep σ G e
      rw [Finset.mem_inter, mem_delta_iff G _ e _ _ hab] at h
      simp at h
    exact (new_mem G σ S 0 j hj hS e (new_edge G σ 0 j hj e he h2)).1
  | succ m ih =>
    intro j hj hS
    have hm : m + 1 < n := by have := j.isLt; omega
    set w : Fin n := ⟨m + 1, hm⟩ with hw
    have hnew : ∀ D : Finset E, (D = C G σ S (m + 1) j ∨ D = C G σ S (m + 1) w) →
        (G.delta (pre σ (m + 1 + 1)) ∩ G.delta {σ j}) \
          (G.delta (pre σ (m + 1)) ∩ G.delta {σ j}) ⊆ C G σ S (m + 1 + 1) j \ D := by
      intro D hD e he
      rw [Finset.mem_sdiff] at he
      have hends := new_edge G σ (m + 1) j hj e he.1 he.2
      have := new_mem G σ S (m + 1) j hj hS e hends
      rw [Finset.mem_sdiff]
      rcases hD with rfl | rfl
      · exact ⟨this.1, this.2.1⟩
      · exact ⟨this.1, this.2.2⟩
    by_cases hsame : (σ w ∈ S ↔ σ ⟨m, by omega⟩ ∈ S)
    · -- `v_{m+1}` on the side of `v_m`: use the induction hypothesis at `j`
      have hS' : ¬ (σ j ∈ S ↔ σ ⟨m, by have := j.isLt; omega⟩ ∈ S) := by
        intro h; exact hS (h.trans hsame.symm)
      refine step G hu (ih j (by omega) hS') ?_ (hnew _ (Or.inl rfl))
      intro e he
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      refine ⟨he.1, fun a ha => ?_⟩
      rcases he.2 a ha with h | h
      · left; omega
      · right; exact h
    · -- `v_{m+1}` active: legal ordering then the induction hypothesis at `w`
      have hS' : ¬ (σ w ∈ S ↔ σ ⟨m, by omega⟩ ∈ S) := hsame
      have hw1 := ih w (by simp [hw]) hS'
      have hleg := hσ w j (by simp [hw]) (by rw [Fin.lt_def]; simp [hw]; omega)
      rw [pre_eq] at hleg
      refine step G hu (hleg.trans hw1) ?_ (hnew _ (Or.inr rfl))
      intro e he
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      refine ⟨he.1, fun a ha => ?_⟩
      rcases he.2 a ha with h | h
      · left; omega
      · left; rw [h]; simp [hw]

end CombOpt.MinCut.LegalOrd

open CombOpt.MinCut.LegalOrd in
open CombOpt.MinCut in
theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E)
    (hu : ∀ e, 0 ≤ G.u e) {n : ℕ} (hn : 2 ≤ n) (σ : Fin n ≃ V) (hσ : G.IsLegalOrdering σ) :
    G.IsMinCut {σ ⟨n - 1, by omega⟩} (σ ⟨n - 1, by omega⟩) (σ ⟨n - 2, by omega⟩) := by
  classical
  have hne : σ ⟨n - 1, by omega⟩ ≠ σ ⟨n - 2, by omega⟩ := by
    intro h; have := congrArg Fin.val (σ.injective h); simp at this; omega
  refine ⟨?_, ?_⟩
  · unfold Separates
    simp [hne.symm]
  · intro T hT
    unfold Separates at hT
    have hT' : ¬ (σ ⟨n - 1, by omega⟩ ∈ T ↔ σ ⟨n - 2, by omega⟩ ∈ T) := by
      rw [xor_iff_not_iff] at hT; exact hT
    have hk := key G hu σ hσ T (n - 2) ⟨n - 1, by omega⟩ (by simp; omega)
      (by
        have e : n - 2 = n - 2 := rfl
        exact hT')
    have h1 : G.delta {σ ⟨n - 1, by omega⟩} ⊆
        G.delta (pre σ (n - 2 + 1)) ∩ G.delta {σ ⟨n - 1, by omega⟩} := by
      intro e he
      refine Finset.mem_inter.2 ⟨?_, he⟩
      obtain ⟨a, b, hab⟩ := ends_rep σ G e
      rw [mem_delta_iff G _ e _ _ hab] at he ⊢
      simp only [mem_pre, Finset.mem_singleton, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff] at he ⊢
      have := a.isLt; have := b.isLt
      omega
    have h2 : C G σ T (n - 2 + 1) ⟨n - 1, by omega⟩ ⊆ G.delta T := by
      intro e he
      simp only [C, Finset.mem_filter] at he
      exact he.2.1
    exact (uSum_mono G hu h1).trans (hk.trans (uSum_mono G hu h2))
