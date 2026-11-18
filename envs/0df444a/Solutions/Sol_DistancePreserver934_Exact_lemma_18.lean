-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:02:22.756162+00:00
-- url     : https://prove2.me/submissions/ee735525-5d1e-431a-9525-c1924fb1da2e

import Definitions.Def_DistancePreserver934_Exact_LoyalCore

set_option autoImplicit false
open Classical DistancePreserver934.Exact

private lemma greedy {V : Type} [Fintype V] (B : V → Finset V)
    (hB : ∀ x, (B x).Nonempty) (W : Finset V) :
    ∃ (C : Finset V) (σ : V → V), C ⊆ W ∧
      (∀ x ∈ W, σ x ∈ C) ∧ (∀ c ∈ C, σ c = c) ∧
      (∀ x ∈ W, ¬ Disjoint (B x) (B (σ x))) ∧
      (∀ x ∈ W, (B x).card ≤ (B (σ x)).card) ∧
      (C : Set V).PairwiseDisjoint B := by
  classical
  induction W using Finset.strongInductionOn
  rename_i W ih
  by_cases hw : W.Nonempty
  · obtain ⟨c,hc,hmax⟩ := Finset.exists_max_image W (fun x => (B x).card) hw
    let U := W.filter (fun x => Disjoint (B x) (B c))
    have hUW : U ⊂ W := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have : c ∈ U := heq.symm ▸ hc
      have hdis := (Finset.mem_filter.mp this).2
      obtain ⟨v,hv⟩ := hB c
      exact Finset.disjoint_left.mp hdis hv hv
    obtain ⟨C,σ,hCW,hσC,hfix,hmeet,hvol,hdis⟩ := ih U hUW
    have hcU : c ∉ U := by
      intro h
      obtain ⟨v,hv⟩ := hB c
      exact Finset.disjoint_left.mp (Finset.mem_filter.mp h).2 hv hv
    have hcC : c ∉ C := fun h => hcU (hCW h)
    let σ' : V → V := fun x => if x ∈ U then σ x else c
    refine ⟨insert c C, σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hc (hCW.trans (Finset.filter_subset _ _))
    · intro x hx
      dsimp [σ']
      split_ifs with h
      · exact Finset.mem_insert_of_mem (hσC x h)
      · exact Finset.mem_insert_self _ _
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [σ', hcU]
      · have hxU := hCW hx
        simpa [σ', hxU] using hfix x hx
    · intro x hx
      dsimp [σ']
      split_ifs with h
      · exact hmeet x h
      · simpa only [U, Finset.mem_filter, hx, true_and] using h
    · intro x hx
      dsimp [σ']
      split_ifs with h
      · exact hvol x h
      · exact hmax x hx
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact (Finset.mem_filter.mp (hCW hy)).2.symm
      · exact (Finset.mem_filter.mp (hCW hx)).2
      · exact hdis hx hy hxy
  · have hz : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hw
    subst W
    exact ⟨∅, id, by simp⟩

private lemma ball_nonempty {V : Type} [Fintype V] (H : SimpleGraph V) (x : V)
    (a : ℝ) (ha : 0 ≤ a) : (ball H x a).Nonempty := by
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by simp, by simpa using ha⟩⟩

private lemma ball_meet {V : Type} [Fintype V] (H : SimpleGraph V) (x c : V)
    (a : ℝ) (h : ¬ Disjoint (ball H x a) (ball H c a)) : x ∈ ball H c (2*a) := by
  classical
  obtain ⟨v,hv1,hv2⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨k,hk,hka⟩ := (Finset.mem_filter.mp hv1).2
  obtain ⟨l,hl,hla⟩ := (Finset.mem_filter.mp hv2).2
  have hh : H.edist c x ≤ ((l+k : ℕ) : ℕ∞) := by
    calc
      _ ≤ H.edist c v + H.edist v x := SimpleGraph.edist_triangle
      _ = ((l+k : ℕ) : ℕ∞) := by rw [SimpleGraph.edist_comm (u := v), hk, hl]; simp
  obtain ⟨j,hj,hjle⟩ := ENat.le_natCast_iff.mp hh
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, ?_⟩
  have hjle' : (j : ℝ) ≤ (l : ℝ) + k := by exact_mod_cast hjle
  linarith


theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) (n : ℕ)
    (hV : Fintype.card V ≤ n) (W : Finset V) (a : ℝ) (ha : 0 < a) :
    ∃ (Cs : Finset V) (σ : V → V), Cs ⊆ W ∧ (∀ x ∈ W, σ x ∈ Cs) ∧
      (∀ c ∈ Cs, ∃ x ∈ W, σ x = c) ∧
      (∀ x ∈ W, x ∈ ball H (σ x) (2 * a)) ∧
      (∀ x ∈ W, vol H x a ≤ vol H (σ x) a) ∧
      ∑ c ∈ Cs, vol H c a ≤ n ∧
      ∑ c ∈ Cs, (W.filter (fun x => σ x = c)).card = W.card ∧ W.card ≤ n := by
  classical
  obtain ⟨Cs,σ,hCW,hassign,hfix,hmeet,hvol,hdis⟩ :=
    greedy (fun x => ball H x a) (fun x => ball_nonempty H x a ha.le) W
  refine ⟨Cs,σ,hCW,hassign,?_,?_,hvol,?_,?_,(Finset.card_le_univ _).trans hV⟩
  · intro c hc
    exact ⟨c,hCW hc,hfix c hc⟩
  · intro x hx
    exact ball_meet H x (σ x) a (hmeet x hx)
  · change ∑ c ∈ Cs, (ball H c a).card ≤ n
    rw [← Finset.card_biUnion hdis]
    exact (Finset.card_le_univ _).trans hV
  · rw [Finset.sum_card_fiberwise_eq_card_filter W Cs σ]
    congr 1
    exact Finset.filter_eq_self.mpr hassign
