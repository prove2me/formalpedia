-- Prove2me | solution 1 for EDPHardness.IntegralityGap.fractional_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:02:28.120194+00:00
-- url     : https://prove2.me/submissions/8502f761-49bd-4763-a67b-7e4fc68f8c18

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPFracSolAux

open EDPHardness.IntegralityGap

variable {n m c : ℕ}

lemma gap_adj (H : Hyp n m c) {a b : Node n m} (hne : a ≠ b) (h : GapRel H a b) :
    (gapGraph H).Adj a b := by
  unfold gapGraph
  rw [SimpleGraph.fromRel_adj]
  exact ⟨hne, Or.inl h⟩

/-- the middle part of the canonical support -/
def mid (L : List (Fin m)) : List (Node n m) :=
  L.flatMap (fun i => [Node.l i, Node.r i])

lemma tail_chain (H : Hyp n m c) (v : Fin n) :
    ∀ (L : List (Fin m)) (i : Fin m), v ∈ (H i).1 → L.Pairwise (· < ·) →
      (∀ j, j ∈ L ↔ (i < j ∧ v ∈ (H j).1)) →
      List.IsChain (gapGraph H).Adj (Node.r i :: (mid L ++ [Node.t v])) := by
  intro L
  induction L with
  | nil =>
    intro i hi _ hiff
    simp only [mid, List.flatMap_nil, List.nil_append]
    refine List.IsChain.cons_cons ?_ (List.isChain_singleton _)
    refine gap_adj H (by simp) (GapRel.last v i hi ?_)
    intro j hj hv
    exact absurd ((hiff j).2 ⟨hj, hv⟩) (by simp)
  | cons j L ih =>
    intro i hi hsort hiff
    have hjL : i < j ∧ v ∈ (H j).1 := (hiff j).1 (by simp)
    rw [List.pairwise_cons] at hsort
    have hrest := ih j hjL.2 hsort.2 (by
      intro k
      constructor
      · intro hk
        exact ⟨hsort.1 k hk, ((hiff k).1 (List.mem_cons_of_mem _ hk)).2⟩
      · rintro ⟨hjk, hvk⟩
        have hk : k ∈ j :: L := (hiff k).2 ⟨lt_trans hjL.1 hjk, hvk⟩
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h (ne_of_gt hjk)
        · exact h)
    have e1 : mid (n := n) (j :: L) ++ [Node.t v] =
        Node.l j :: Node.r j :: (mid L ++ [Node.t v]) := by
      simp [mid]
    rw [e1]
    refine List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ hrest)
    · refine gap_adj H (by simp) (GapRel.consec v i j hjL.1 hi hjL.2 ?_)
      intro k hik hkj hvk
      have hk : k ∈ j :: L := (hiff k).2 ⟨hik, hvk⟩
      rcases List.mem_cons.1 hk with h | h
      · exact absurd h (ne_of_lt hkj)
      · exact absurd (hsort.1 k h) (not_lt.2 hkj.le)
    · exact gap_adj H (by simp) (GapRel.special j)

def idxList (H : Hyp n m c) (v : Fin n) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (v ∈ (H i).1))

lemma idxList_sorted (H : Hyp n m c) (v : Fin n) : (idxList H v).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange m).filter _

lemma mem_idxList (H : Hyp n m c) (v : Fin n) (j : Fin m) :
    j ∈ idxList H v ↔ v ∈ (H j).1 := by
  simp [idxList]

lemma canon_eq (H : Hyp n m c) (v : Fin n) :
    canonicalSupport H v = Node.s v :: (mid (idxList H v) ++ [Node.t v]) := rfl

lemma canon_chain (H : Hyp n m c) (v : Fin n) :
    List.IsChain (gapGraph H).Adj (canonicalSupport H v) := by
  rw [canon_eq]
  have hs := idxList_sorted H v
  have hm := mem_idxList H v
  generalize idxList H v = L at hs hm
  cases L with
  | nil =>
    simp only [mid, List.flatMap_nil, List.nil_append]
    refine List.IsChain.cons_cons ?_ (List.isChain_singleton _)
    refine gap_adj H (by simp) (GapRel.isolated v ?_)
    intro i hi
    exact absurd ((hm i).2 hi) (by simp)
  | cons j L =>
    have hj : v ∈ (H j).1 := (hm j).1 (by simp)
    rw [List.pairwise_cons] at hs
    have e1 : mid (n := n) (j :: L) ++ [Node.t v] =
        Node.l j :: Node.r j :: (mid L ++ [Node.t v]) := by
      simp [mid]
    rw [e1]
    refine List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ ?_)
    · refine gap_adj H (by simp) (GapRel.first v j hj ?_)
      intro k hkj hvk
      have hk : k ∈ j :: L := (hm k).2 hvk
      rcases List.mem_cons.1 hk with h | h
      · exact absurd h (ne_of_lt hkj)
      · exact absurd (hs.1 k h) (not_lt.2 hkj.le)
    · exact gap_adj H (by simp) (GapRel.special j)
    · refine tail_chain H v L j hj hs.2 ?_
      intro k
      constructor
      · intro hk
        exact ⟨hs.1 k hk, (hm k).1 (List.mem_cons_of_mem _ hk)⟩
      · rintro ⟨hjk, hvk⟩
        rcases List.mem_cons.1 ((hm k).2 hvk) with h | h
        · exact absurd h (ne_of_gt hjk)
        · exact h

lemma mid_nodup : ∀ (L : List (Fin m)), L.Nodup → (mid (n := n) L).Nodup := by
  intro L
  induction L with
  | nil => intro _; simp [mid]
  | cons j L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    have e1 : mid (n := n) (j :: L) = Node.l j :: Node.r j :: mid L := by simp [mid]
    rw [e1]
    have hmem : ∀ x, x ∈ mid (n := n) L → x ≠ Node.l j ∧ x ≠ Node.r j := by
      intro x hx
      simp only [mid, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨i, hi, hx⟩ := hx
      have hij : i ≠ j := fun h => hL.1 (h ▸ hi)
      rcases hx with rfl | rfl <;> simp [hij]
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih hL.2⟩⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨by simp, fun h => (hmem _ h).1 rfl⟩
    · exact fun h => (hmem _ h).2 rfl

lemma mid_mem {L : List (Fin m)} {x : Node n m} (hx : x ∈ mid L) :
    ∃ i ∈ L, x = Node.l i ∨ x = Node.r i := by
  simp only [mid, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  exact hx

lemma canon_nodup (H : Hyp n m c) (v : Fin n) : (canonicalSupport H v).Nodup := by
  rw [canon_eq]
  have hL : (idxList H v).Nodup := (idxList_sorted H v).imp (fun h => ne_of_lt h)
  have hmid := mid_nodup (n := n) _ hL
  refine List.nodup_cons.2 ⟨?_, ?_⟩
  · intro h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨i, _, hx | hx⟩ := mid_mem h <;> cases hx
    · simp at h
  · refine List.nodup_append.2 ⟨hmid, by simp, ?_⟩
    intro a ha b hb hab
    simp at hb
    subst hb; subst hab
    obtain ⟨i, _, hx | hx⟩ := mid_mem ha <;> cases hx

lemma canon_mem (H : Hyp n m c) (v : Fin n) (x : Node n m) (hx : x ∈ canonicalSupport H v) :
    x = Node.s v ∨ x = Node.t v ∨ ∃ i, v ∈ (H i).1 ∧ (x = Node.l i ∨ x = Node.r i) := by
  rw [canon_eq] at hx
  rcases List.mem_cons.1 hx with h | h
  · exact Or.inl h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨i, hi, hx⟩ := mid_mem h
    exact Or.inr (Or.inr ⟨i, (mem_idxList H v i).1 hi, hx⟩)
  · simp at h
    exact Or.inr (Or.inl h)

lemma canon_ne (H : Hyp n m c) (v : Fin n) : canonicalSupport H v ≠ [] := by
  rw [canon_eq]; simp

lemma canon_head (H : Hyp n m c) (v : Fin n) :
    (canonicalSupport H v).head (canon_ne H v) = src n m v := by
  simp [canon_eq, src]

lemma canon_last (H : Hyp n m c) (v : Fin n) :
    (canonicalSupport H v).getLast (canon_ne H v) = snk n m v := by
  simp [canon_eq, snk]

/-- the canonical path as a walk -/
def canonWalk (H : Hyp n m c) (v : Fin n) : (gapGraph H).Walk (src n m v) (snk n m v) :=
  (SimpleGraph.Walk.ofSupport (canonicalSupport H v) (canon_ne H v) (canon_chain H v)).copy
    (canon_head H v) (canon_last H v)

lemma canonWalk_support (H : Hyp n m c) (v : Fin n) :
    (canonWalk H v).support = canonicalSupport H v := by
  unfold canonWalk
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]

lemma canonWalk_isPath (H : Hyp n m c) (v : Fin n) : (canonWalk H v).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, canonWalk_support]
  exact canon_nodup H v

lemma card_through (H : Hyp n m c) (a : Node n m) (hc : 1 ≤ c) :
    (Finset.univ.filter (fun v : Fin n => a ∈ canonicalSupport H v)).card ≤ c := by
  cases a with
  | s w =>
    calc _ ≤ ({w} : Finset (Fin n)).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases canon_mem H v _ hv with h | h | ⟨i, _, h | h⟩ <;> cases h
          simp
      _ ≤ c := by simpa using hc
  | t w =>
    calc _ ≤ ({w} : Finset (Fin n)).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases canon_mem H v _ hv with h | h | ⟨i, _, h | h⟩ <;> cases h
          simp
      _ ≤ c := by simpa using hc
  | l j =>
    calc _ ≤ (H j).1.card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases canon_mem H v _ hv with h | h | ⟨i, hi, h | h⟩ <;> cases h
          exact hi
      _ = c := (H j).2
  | r j =>
    calc _ ≤ (H j).1.card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases canon_mem H v _ hv with h | h | ⟨i, hi, h | h⟩ <;> cases h
          exact hi
      _ = c := (H j).2

theorem main (H : Hyp n m c) (hc : 2 ≤ c) :
    ∃ F : FracSol (gapGraph H) (src n m) (snk n m),
      F.value = (n : ℝ) / c ∧
      ∀ v, ∀ P ∈ F.paths v, P.support = canonicalSupport H v ∧ F.f v P = 1 / (c : ℝ) := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hc1 : 1 / (c : ℝ) ≤ 1 := by
    rw [div_le_one hcpos]; exact_mod_cast (by omega : 1 ≤ c)
  refine ⟨{ paths := fun v => {canonWalk H v}
            f := fun _ _ => 1 / (c : ℝ)
            isPath := ?_
            f_nonneg := ?_
            f_le_one := ?_
            x_le_one := ?_
            capacity := ?_ }, ?_, ?_⟩
  · intro v P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact canonWalk_isPath H v
  · intro _ _ _; positivity
  · intro _ _ _; exact hc1
  · intro v; simpa using hc1
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
    have key : ∀ v : Fin n,
        (∑ P ∈ (({canonWalk H v} : Finset ((gapGraph H).Walk (src n m v) (snk n m v))).filter
          (fun P => s(a, b) ∈ P.edges)), (1 / (c : ℝ))) ≤
        if a ∈ canonicalSupport H v then 1 / (c : ℝ) else 0 := by
      intro v
      rw [Finset.filter_singleton]
      split_ifs with h1 h2 h2
      · simp
      · exfalso
        apply h2
        rw [← canonWalk_support]
        exact SimpleGraph.Walk.fst_mem_support_of_mem_edges _ h1
      · simp
      · simp
    calc _ ≤ ∑ v : Fin n, (if a ∈ canonicalSupport H v then 1 / (c : ℝ) else 0) :=
          Finset.sum_le_sum (fun v _ => key v)
      _ = ((Finset.univ.filter (fun v : Fin n => a ∈ canonicalSupport H v)).card : ℝ) *
            (1 / (c : ℝ)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (c : ℝ) * (1 / (c : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_through H a (by omega)
      _ = 1 := by field_simp
  · simp [FracSol.value, FracSol.x]
    field_simp
  · intro v P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨canonWalk_support H v, rfl⟩

end EDPFracSolAux

open EDPHardness.IntegralityGap in
theorem solution (n c : ℕ) (hc : 2 ≤ c) (H : Hyp n (numEdges n c) c) :
    ∃ F : FracSol (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)),
      F.value = (n : ℝ) / c ∧
      ∀ v, ∀ P ∈ F.paths v, P.support = canonicalSupport H v ∧ F.f v P = 1 / (c : ℝ) :=
  EDPFracSolAux.main H hc
