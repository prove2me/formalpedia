-- Prove2me | solution 1 for FlowsNetworks.Graphs.independent_arcs_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:47:30.680391+00:00
-- url     : https://prove2.me/submissions/b966428f-737b-4eab-9c37-da7aacc94a3d

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_PosetGraph
open FlowsNetworks.Graphs


def g69e_JChain {n : ℕ} (J : Finset (Fin n × Fin n)) (C : Finset (Fin n)) : Prop :=
  ∃ l : List (Fin n), l ≠ [] ∧ l.Nodup ∧ (∀ a, a ∈ C ↔ a ∈ l) ∧
    List.IsChain (fun a b => (a, b) ∈ J) l

theorem g69e_ind_gen {n : ℕ} (r : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) r]
    (J : Finset (Fin n × Fin n)) (hJ : IsIndependentArcs r J) :
    ∃ Q : Finset (Finset (Fin n)), (∀ A ∈ Q, ∀ B ∈ Q, A ≠ B → Disjoint A B) ∧
      (∀ a, ∃ C ∈ Q, a ∈ C) ∧ (∀ C ∈ Q, g69e_JChain J C) ∧ J.card + Q.card = n := by
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨Finset.univ.image (fun a => {a}), ?_, ?_, ?_, ?_⟩
    · simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
      rw [Finset.disjoint_singleton]
      exact fun h => hab (by rw [h])
    · intro a; exact ⟨{a}, by simp, by simp⟩
    · simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨a, rfl⟩
      exact ⟨[a], by simp, by simp, by simp, List.isChain_singleton a⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => Finset.singleton_injective h)]
      simp
  | insert e J' he ih =>
    obtain ⟨i, j⟩ := e
    have hJ' : IsIndependentArcs r J' := ⟨fun p hp => hJ.1 p (Finset.mem_insert_of_mem hp),
      fun p hp q hq hpq => hJ.2 p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq⟩
    obtain ⟨Q', hdis, hcov, hch, hcard⟩ := ih hJ'
    have hrij : r i j := hJ.1 _ (Finset.mem_insert_self _ _)
    -- independence consequences
    have hfst : ∀ k, (i, k) ∈ J' → False := by
      intro k hk
      have := hJ.2 (i, j) (Finset.mem_insert_self _ _) (i, k) (Finset.mem_insert_of_mem hk)
        (fun h => he (h ▸ hk))
      exact this.1 rfl
    have hsnd : ∀ k, (k, j) ∈ J' → False := by
      intro k hk
      have := hJ.2 (i, j) (Finset.mem_insert_self _ _) (k, j) (Finset.mem_insert_of_mem hk)
        (fun h => he (h ▸ hk))
      exact this.2 rfl
    obtain ⟨C1, hC1, hiC1⟩ := hcov i
    obtain ⟨C2, hC2, hjC2⟩ := hcov j
    obtain ⟨l1, hl1ne, hl1nd, hl1m, hl1c⟩ := hch C1 hC1
    obtain ⟨l2, hl2ne, hl2nd, hl2m, hl2c⟩ := hch C2 hC2
    -- i is last in l1
    obtain ⟨a1, b1, rfl⟩ := List.append_of_mem ((hl1m i).1 hiC1)
    have hb1 : b1 = [] := by
      rcases b1 with _ | ⟨k, b1⟩
      · rfl
      · exfalso
        rw [List.isChain_append] at hl1c
        have := List.isChain_cons_cons.1 hl1c.2.1
        exact hfst k this.1
    subst hb1
    -- j is first in l2
    obtain ⟨a2, b2, rfl⟩ := List.append_of_mem ((hl2m j).1 hjC2)
    have ha2 : a2 = [] := by
      rcases List.eq_nil_or_concat a2 with h | ⟨L, k, rfl⟩
      · exact h
      · exfalso
        rw [List.isChain_append] at hl2c
        have := hl2c.2.2 k (by simp) j (by simp)
        exact hsnd k this
    subst ha2
    simp only [List.nil_append] at *
    have hC12 : C1 ≠ C2 := by
      intro h
      subst h
      -- j :: b2 is a chain containing i
      have hi2 : i ∈ j :: b2 := (hl2m i).1 hiC1
      have hpw : List.Pairwise r (j :: b2) := by
        rw [← List.isChain_iff_pairwise]
        exact List.IsChain.imp (fun a b h => hJ.1 (a, b) (Finset.mem_insert_of_mem h)) hl2c
      rcases List.mem_cons.1 hi2 with h | h
      · subst h; exact irrefl _ hrij
      · exact asymm hrij ((List.pairwise_cons.1 hpw).1 i h)
    have hd12 : Disjoint C1 C2 := hdis C1 hC1 C2 hC2 hC12
    set Q := insert (C1 ∪ C2) ((Q'.erase C1).erase C2) with hQ
    have hnotin : C1 ∪ C2 ∉ (Q'.erase C1).erase C2 := by
      intro h
      simp only [Finset.mem_erase] at h
      have := hdis _ h.2.2 C1 hC1 h.2.1
      exact (Finset.disjoint_left.1 this) (Finset.mem_union_left _ hiC1) hiC1
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · have hD : ∀ D ∈ (Q'.erase C1).erase C2, Disjoint (C1 ∪ C2) D := by
        intro D hD
        simp only [Finset.mem_erase] at hD
        exact Finset.disjoint_union_left.2 ⟨hdis C1 hC1 D hD.2.2 (Ne.symm hD.2.1),
          hdis C2 hC2 D hD.2.2 (Ne.symm hD.1)⟩
      intro A hA B hB hAB
      rw [hQ, Finset.mem_insert] at hA hB
      rcases hA with rfl | hA <;> rcases hB with rfl | hB
      · exact absurd rfl hAB
      · exact hD B hB
      · exact (hD A hA).symm
      · simp only [Finset.mem_erase] at hA hB
        exact hdis A hA.2.2 B hB.2.2 hAB
    · intro a
      obtain ⟨C, hC, haC⟩ := hcov a
      by_cases h1 : C = C1
      · subst h1; exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_left _ haC⟩
      by_cases h2 : C = C2
      · subst h2; exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_right _ haC⟩
      exact ⟨C, Finset.mem_insert_of_mem (by simp [h1, h2, hC]), haC⟩
    · have hmono : ∀ l : List (Fin n), List.IsChain (fun a b => (a, b) ∈ J') l →
          List.IsChain (fun a b => (a, b) ∈ insert (i, j) J') l :=
        fun l h => List.IsChain.imp (fun a b h => Finset.mem_insert_of_mem h) h
      intro C hC
      rw [hQ, Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · refine ⟨(a1 ++ [i]) ++ (j :: b2), by simp, ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hl1nd, hl2nd, ?_⟩
          intro x hx y hy hxy
          subst hxy
          exact (Finset.disjoint_left.1 hd12) ((hl1m x).2 hx) ((hl2m x).2 hy)
        · intro x
          rw [Finset.mem_union, hl1m, hl2m]; simp only [List.mem_append]
        · rw [List.isChain_append]
          refine ⟨hmono _ hl1c, hmono _ hl2c, ?_⟩
          intro x hx y hy
          simp at hx hy
          subst hx hy
          exact Finset.mem_insert_self _ _
      · simp only [Finset.mem_erase] at hC
        obtain ⟨l, h1, h2, h3, h4⟩ := hch C hC.2.2
        exact ⟨l, h1, h2, h3, hmono l h4⟩
    · rw [Finset.card_insert_of_notMem he, hQ, Finset.card_insert_of_notMem hnotin,
        Finset.card_erase_of_mem (by simp [Ne.symm hC12, hC2]), Finset.card_erase_of_mem hC1]
      have : 2 ≤ Q'.card := by
        have : ({C1, C2} : Finset _) ⊆ Q' := by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl | rfl) <;> assumption
        have h := Finset.card_le_card this
        rwa [Finset.card_pair hC12] at h
      omega


/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Lemma 8.1 (p. 46). Let `P = {1, …, n}` be
partially ordered by `≻` (`r`, a strict partial order) and let `G = [S, T; 𝒜]` be the bipartite
graph with `(x_i, y_j) ∈ 𝒜` iff `i ≻ j`. Corresponding to any independent set `𝒥 ⊆ 𝒜` there is a
decomposition `Δ` of `P` with `|𝒥| + |Δ| = n`. -/
theorem solution {n : ℕ} (r : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) r]
    (J : Finset (Fin n × Fin n)) (hJ : IsIndependentArcs r J) :
    ∃ Δ : Finpartition (Finset.univ : Finset (Fin n)),
      IsDecomposition r Δ ∧ J.card + Δ.parts.card = n := by
  obtain ⟨Q, hdis, hcov, hch, hcard⟩ := g69e_ind_gen r J hJ
  have hne : ∀ C ∈ Q, C.Nonempty := by
    intro C hC
    obtain ⟨l, h1, -, h3, -⟩ := hch C hC
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l h1
    exact ⟨a, (h3 a).2 ha⟩
  refine ⟨⟨Q, ?_, ?_, ?_⟩, ?_, hcard⟩
  · rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    exact hdis A hA B hB hAB
  · ext a
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨C, hC, haC⟩ := hcov a
    exact Finset.mem_sup.2 ⟨C, hC, haC⟩
  · intro h
    obtain ⟨a, ha⟩ := hne ⊥ h
    simp at ha
  · intro C hC
    obtain ⟨l, h1, h2, h3, h4⟩ := hch C hC
    refine ⟨l, h1, h2, h3, ?_⟩
    have := List.isChain_iff_getElem.1 h4
    intro m hm
    exact hJ.1 _ (this m hm)

